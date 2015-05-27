// -*- tab-width:4 ; indent-tabs-mode:nil -*-
#include <hre/config.h>
#include <hre/user.h>
#include <dm/dm.h>
#include <ltsmin-lib/ltsmin-standard.h>
#include <pins-lib/dlopen-pins.h>
#include <pins-lib/dlopen-api.h>
#include <util-lib/rationals.h>
#include <hre/stringindex.h>
#include <scoop.h>

static int check_confluence=0;
static int enable_rewards=0;
static int internal_max_progress=1;
static int iomapa=0;

static const char const_long[]="const";
static const char progress_long[]="max-progress";
#define IF_LONG(long) if(((opt->longName)&&!strcmp(opt->longName,long)))

void prcrl_load_model(model_t model,const char*name);
void mapa_load_model(model_t model,const char*name);


static enum {
    MAX_PROGRESS_NONE=0,
    MAX_PROGRESS_TAU=1,
    MAX_PROGRESS_ALL=2
} max_progress=MAX_PROGRESS_ALL;

static void poptCallback(poptContext con,
 		enum poptCallbackReason reason,
                            const struct poptOption * opt,
                             const char * arg, void * data){
	(void)con;(void)opt;(void)arg;(void)data;
	switch(reason){
	case POPT_CALLBACK_REASON_PRE:
	{
	    char *argv[2];
        argv[0]=get_label();
        argv[1]=NULL;
        scoop_init(1,argv);
		return;
    }
	case POPT_CALLBACK_REASON_POST:
	{
	    GBregisterLoader("prcrl",prcrl_load_model);
	    GBregisterLoader("mapa",mapa_load_model);
		Warning(infoLong,"MAPA language module initialized");
		return;
    }
	case POPT_CALLBACK_REASON_OPTION:
	    IF_LONG(const_long){
	        Warning(info,"Definition %s",arg);
	        char*val=strchr(arg,'=');
	        if (val==NULL) {
	            Abort("illegal use of %s option",const_long);
	        }
	        *val=0;
	        val++;
	        scoop_put_constant(arg,val);
	        Warning(info,"Definition %s = %s",arg,val);
	    }
	    IF_LONG(progress_long){
	        Warning(info,"maximal progress %s",arg);
	        if (strcmp(arg,"none")==0){
	            max_progress=MAX_PROGRESS_NONE;
	            return;
	        }
	        if (strcmp(arg,"tau")==0){
	            max_progress=MAX_PROGRESS_TAU;
	            return;
	        }
	        if (strcmp(arg,"all")==0){
	            max_progress=MAX_PROGRESS_ALL;
	            return;
	        }
	        Abort("Unknown maximal progress version %s",arg);
	    }
	    // ignore all other options.
		return;
	}
	Abort("unexpected call to scoop plugin callback");
}

struct poptOption mapa_options[]= {
    { NULL, 0 , POPT_ARG_CALLBACK|POPT_CBFLAG_PRE|POPT_CBFLAG_POST , poptCallback , 0 , NULL , NULL },
    { const_long , 0 , POPT_ARG_STRING , NULL , 0, "define constant <var> as <val>","<var>=<val>" },
    { progress_long , 0 , POPT_ARG_STRING , NULL , 0,
     "Specify the set of actions for which maximal progress has to be enabled."
     " The default is 'all', meaning that all actions are prioritised."
     " The other settings are 'tau', to prioritise just the tau steps"
     " and 'none' to disable maximal progress","<actions>"},
    { "rewards" , 0 , POPT_ARG_VAL, &enable_rewards , 1, "enable edge rewards" , NULL },
    { "confluence", 0, POPT_ARG_VAL, &check_confluence, 1, "detect confluent summands and write confluent matrix", NULL },
    { "external-max-progress", 0 , POPT_ARG_VAL , & internal_max_progress , 0 ,
      "By default the getTransitionsAll method will apply maximal progress."
      " This option allows external handling of maximal progress for that call." , NULL },
	POPT_TABLEEND
};

static string_index_t reach_actionss[10];
static int action_types[10];
static int state_lengths[10];
static int *state_types[10];
static model_t main_models[10];
static int *cb_dests[10];
static int cb_labels[10][7];
static int model_count = 0;
static int model_nr = 0;

static TransitionCB user_cb;
static void* cb_ctx;

void report_reach(char* str){
    SIput(reach_actionss[model_nr],str);
}


static void scoop_rationalize(char*str,int*label){
    char* ptr=strrchr(str,'/');
    if (ptr==NULL) {
        float f=atof(str);
        rationalize32(f,(uint32_t*)label+4,(uint32_t*)label+5);
    } else {
        label[4]=atoi(str);
        ptr++;
        label[5]=atoi(ptr);
    }
}
void write_prob_label(char *str,int*label){
    Warning(infoLong,"prob label %s=",str);
    scoop_rationalize(str,label);
    Warning(infoLong,"  %d/%d",label[4],label[5]);
}

void write_rate_label(char *str,int*label){
    Warning(infoLong,"rate label %s=",str);
    scoop_rationalize(str+5,label);
    Warning(infoLong,"  %d/%d",label[4],label[5]);
}

int get_numerator(char *str){
    return atoi(str);
}

int get_denominator(char *str){
    char* ptr=strrchr(str,'/');
    if (ptr==NULL) return 1;
    ptr++;
    return atoi(ptr);
}

void write_reward_label(char *str,int*label){
    Warning(infoLong,"reward label %s=",str);
    float f=atof(str);
    if(f>0){
        rationalize32(f,(uint32_t*)label+0,(uint32_t*)label+1);
        Warning(infoLong,"  %d/%d",label[0],label[1]);
    }
}

int action_get_index(char* val){
    int res=GBchunkPut(main_models[model_nr],action_types[model_nr],chunk_str(val));
//    extra_chunks(action_types[model_nr],chunk_str(val));
//    Warning(info,"get action index for %s : %d",val,res);
    return res;
}

int term_get_index(int pos,char* val){
    int res=GBchunkPut(main_models[model_nr],state_types[model_nr][pos],chunk_str(val));
//    extra_chunks(action_types[model_nr],chunk_str(val));
//    Warning(info,"get %d index (%d) for %s : %d",pos,state_types[model_nr][pos],val,res);
    return res;
}

char* term_get_value(int pos,int idx){
    chunk res=GBchunkGet(main_models[model_nr],state_types[model_nr][pos],idx);
//    Warning(info,"ModelNr:%d\nState_Type:%d\nidx:%d\npos:%d",model_nr,state_types[model_nr][pos],idx,pos);
//    Warning(info, "%S", res.data);
    return res.data;
}


void prcrl_callback(void){
//	int lbl=ATfindIndex(actionmap,label);
//    transition_info_t ti = GB_TI(&lbl, -1);
    transition_info_t ti = GB_TI(cb_labels[model_nr], -1);
//    Warning(info, "to(%d,%d)", cb_dests[model_nr][0], cb_dests[model_nr][1]);
	user_cb(cb_ctx,&ti,cb_dests[model_nr],NULL);
}

static void discard_callback(void*context,transition_info_t*info,int*dst,int*src){
    (void)context;
    (void)info;
    (void)dst;
    (void)src;
}

#define HsStablePtr void*

typedef struct prcrl_context {
    model_t cached;
    HsStablePtr spec;
    string_index_t reach_actions;
    matrix_t reach_info;
    matrix_t class_matrix;
} *prcrl_context_t;

static int PRCRLdelegateTransitionsLong(model_t model,int group,int*src,TransitionCB cb,void*context){
    prcrl_context_t ctx=GBgetContext(model);
    model_nr = GBgetModelNr(model);
    return GBgetTransitionsLong(ctx->cached,group,src,cb,context);
}

static int PRCRLgetTransitionsLong(model_t model,int group,int*src,TransitionCB cb,void*context){
    prcrl_context_t ctx=GBgetContext(model);
    model_nr = GBgetModelNr(model);
    cb_ctx=context;
    user_cb=cb;
//    Warning(info, "from(%d,%d)", src[0], src[1]);
    int res=prcrl_explore_long(ctx->spec,group,src,cb_dests[model_nr],cb_labels[model_nr]);
    return res;
}


static int PRCRLgetTransitionsAll(model_t model,int*src,TransitionCB cb,void*context){
    int res=0;
    switch(max_progress){
    case MAX_PROGRESS_NONE:{
        int N=dm_nrows(GBgetDMInfo(model));
      	for(int i=0; i < N ; i++) {
    		res+=GBgetTransitionsLong(model,i,src,cb,context);
    	}
    	break;
	}
    case MAX_PROGRESS_TAU:{
        prcrl_context_t ctx=GBgetContext(model);
        res=GBgetTransitionsMarked(model,&ctx->class_matrix,0,src,cb,context);
        if (res==0){
            res+=GBgetTransitionsMarked(model,&ctx->class_matrix,2,src,cb,context);
        }
        res+=GBgetTransitionsMarked(model,&ctx->class_matrix,1,src,cb,context);
        break;
    }
    case MAX_PROGRESS_ALL:{
        prcrl_context_t ctx=GBgetContext(model);
        res=GBgetTransitionsMarked(model,&ctx->class_matrix,0,src,cb,context);
        res+=GBgetTransitionsMarked(model,&ctx->class_matrix,1,src,cb,context);
        if (res==0){
            res+=GBgetTransitionsMarked(model,&ctx->class_matrix,2,src,cb,context);
        }
        break;
    }}
    return res;
}

static int label_actions(char*edge_class){
    return SIlookup(reach_actionss[model_nr],edge_class)>=0;
}

static void get_state_labels(model_t self,int*src,int *label){
    prcrl_context_t ctx=GBgetContext(self);

    if (enable_rewards){
        prcrl_get_state_reward(ctx->spec,(uint32_t*)src,(uint32_t*)label+1);
        Warning(info,"state reward %u/%u",label[1],label[2]);
    } else {
        label[1]=0;
        label[2]=1;
    }
    
    matrix_t *dm_reach=&ctx->reach_info;
    int N=dm_ncols(dm_reach);
    label[0]=0;
    for (int i=0;i<N;i++){
      if (dm_is_set(dm_reach,0,i)){
        if (GBgetTransitionsLong(self,i,src,discard_callback,NULL)){
            label[0]=1;
            break;
        }
      }
    }
}

static int get_state_label(model_t self, int l, int *src) {
    HREassert(l >=0 && l < 3, "invalid state label %d", l);
    int labels[3];
    get_state_labels(self, src, labels);
    return labels[l];
}

void common_load_model(model_t model,const char*name,int mapa){
    Warning(infoLong,"Loading %s",name);
    model_nr = GBgetModelNr(model);
    prcrl_context_t context=RT_NEW(struct prcrl_context);
    GBsetContext(model,context);
    main_models[model_count]=model;
    context->reach_actions=reach_actionss[model_count]=SIcreate();
    if (mapa){
        if(iomapa){
            context->spec=scoop_load_mapa((char*)name, "true");
        } else {
            context->spec=scoop_load_mapa((char*)name, "false");
        }
    } else {
        context->spec=scoop_load_prcrl((char*)name);
    }

   	lts_type_t ltstype=lts_type_create();
   	int bool_type=lts_type_put_type(ltstype,"Bool",LTStypeChunk,NULL);


	int N=prcrl_pars(context->spec);
	int nSmds=prcrl_summands(context->spec);
	int nRewards=prcrl_rewards(context->spec);
	Warning(info,"spec has %d rewards",nRewards);

	state_lengths[model_count]=N;
	lts_type_set_state_length(ltstype,N);
	Warning(infoLong,"spec has %d parameters",N);
	state_types[model_count]=(int*)RTmalloc(N*sizeof(int));
	cb_dests[model_count]=(int*)RTmalloc(N*sizeof(int));
	for(int i=0;i<N;i++){
	    char* v=prcrl_par_name(context->spec,i);
	    char* t=prcrl_par_type(context->spec,i);
	    Warning(infoLong,"%s: %s",v,t);
	    state_types[model_count][i]=lts_type_put_type(ltstype,t,LTStypeChunk,NULL);
	    lts_type_set_state_name(ltstype,i,v);
	    lts_type_set_state_type(ltstype,i,t);
	}	
	// TODO: set proper edge types!
	action_types[model_count]=lts_type_put_type(ltstype,"action",LTStypeChunk,NULL);
    lts_type_put_type(ltstype,"nat",LTStypeDirect,NULL);
    lts_type_put_type(ltstype,"pos",LTStypeDirect,NULL);

    lts_type_set_edge_label_count(ltstype,6);
    lts_type_set_edge_label_name(ltstype,0,"reward_numerator");
    lts_type_set_edge_label_type(ltstype,0,"nat");
    lts_type_set_edge_label_name(ltstype,1,"reward_denominator");
    lts_type_set_edge_label_type(ltstype,1,"pos");
    lts_type_set_edge_label_name(ltstype,2,LTSMIN_EDGE_TYPE_ACTION_PREFIX);
    lts_type_set_edge_label_type(ltstype,2,LTSMIN_EDGE_TYPE_ACTION_PREFIX);
    lts_type_set_edge_label_name(ltstype,3,"group");
    lts_type_set_edge_label_type(ltstype,3,"nat");
    lts_type_set_edge_label_name(ltstype,4,"numerator");
    lts_type_set_edge_label_type(ltstype,4,"nat");
    lts_type_set_edge_label_name(ltstype,5,"denominator");
    lts_type_set_edge_label_type(ltstype,5,"pos");
    if(!iomapa){
        dm_create(&context->class_matrix,3,nSmds);
    } else {
        dm_create(&context->class_matrix,5,nSmds);
    }

    lts_type_set_state_label_count(ltstype,3);
    lts_type_set_state_label_name(ltstype,0,"goal");
    lts_type_set_state_label_type(ltstype,0,"Bool");
    lts_type_set_state_label_name(ltstype,1,"state_reward_numerator");
    lts_type_set_state_label_type(ltstype,1,"nat");
    lts_type_set_state_label_name(ltstype,2,"state_reward_denominator");
    lts_type_set_state_label_type(ltstype,2,"pos");

    int reach_smds=0;
    static matrix_t sl_infos[10];
    dm_create(&sl_infos[model_count], 3, state_lengths[model_count]);
    for(int i=0;i<state_lengths[model_count];i++){
        dm_set(&sl_infos[model_count], 1, i);
        dm_set(&sl_infos[model_count], 2, i);
    }
    dm_create(&context->reach_info, 1, nSmds);
    static matrix_t conf_infos[10];
    if(check_confluence){
        Warning(info,"creating confluence matrix");
        dm_create(&conf_infos[model_count], 3, nSmds);
        // row 0 are confluent
        // row 1 are silent
        // row 2 are non-confluence markers
        // a state with precisely one silent step and no non-confluence markers is confluent too.
    }
    for(int i=0;i<nSmds;i++){
        char *action=prcrl_get_action(context->spec,i);
        Warning(infoLong,"summand %d is a %s summand",i,action);
        if (label_actions(action) || strcmp(action,"reachConditionAction")==0){
            Warning(infoLong,"summand %d is a %s reach marked summand",i,action);
            reach_smds++;
            dm_set(&context->reach_info, 0, i);
            for(int j=0;j<state_lengths[model_count];j++){
                if (prcrl_is_used(context->spec,i,j)){
                    dm_set(&sl_infos[model_count], 0, j);
                }
            }
        }
        if (iomapa){
            if (strcmp(action,"tau")==0) {
                if(check_confluence){ // mark entry as silent
                    dm_set(&conf_infos[model_count],1,i);
                }
                dm_set(&context->class_matrix,0,i);
            } else if (strncmp(action,"rate",4)==0) {
                dm_set(&context->class_matrix,4,i);
                // rate steps do not make a tau step non-confluent
            } else {
                if (strcmp(action,"reachConditionAction")!=0 &&
                    strcmp(action,"stateRewardAction")!=0) {
                    if(!iomapa){
                        dm_set(&context->class_matrix,1,i);
                    } else {
                        if (action[strlen(action) - 1] == '?'){
                            dm_set(&context->class_matrix,3,i);//input action
                        } else {
                            if (action[strlen(action) - 1] == '!'){
                                dm_set(&context->class_matrix,2,i);//output action
                            } else {
                                dm_set(&context->class_matrix,1,i);//internal action
                            }
                        }
                    }
                    if(check_confluence){ // other steps make tau steps non-confluent
                        dm_set(&conf_infos[model_count],2,i);
                    }
                }
            }
        } else {
            if (strcmp(action,"tau")==0) {
                if(check_confluence){ // mark entry as silent
                    dm_set(&conf_infos[model_count],1,i);
                }
                dm_set(&context->class_matrix,0,i);
            } else if (strncmp(action,"rate",4)==0) {
                dm_set(&context->class_matrix,2,i);
                // rate steps do not make a tau step non-confluent
            } else {
                if (strcmp(action,"reachConditionAction")!=0 &&
                    strcmp(action,"stateRewardAction")!=0) {
                    dm_set(&context->class_matrix,1,i);
                    if(check_confluence){ // other steps make tau steps non-confluent
                        dm_set(&conf_infos[model_count],2,i);
                    }
                }
            }
        }
    }

	GBsetLTStype(model,ltstype);
    GBchunkPutAt(model,bool_type,chunk_str("F"),0);
    GBchunkPutAt(model,bool_type,chunk_str("T"),1);

    GBsetMatrix(model,LTSMIN_EDGE_TYPE_ACTION_CLASS,&context->class_matrix,PINS_STRICT,PINS_INDEX_OTHER,PINS_INDEX_GROUP);

    FILE *classfile = fopen("class.txt", "w+");
    dm_print(classfile, &context->class_matrix);
    fclose(classfile);


    static matrix_t progress_matrixs[10];
    if(!iomapa){
        if (max_progress != MAX_PROGRESS_NONE){
            dm_create(&progress_matrixs[model_count],3,3);
            dm_set(&progress_matrixs[model_count],0,2);
            if (max_progress == MAX_PROGRESS_ALL) dm_set(&progress_matrixs[model_count],1,2);
            int id=GBsetMatrix(model,"inhibit",&progress_matrixs[model_count],PINS_STRICT,PINS_INDEX_OTHER,PINS_INDEX_OTHER);
            Warning(info,"inhibit matrix registered as %d",id);
        }
    } else { //io markov chain
        if (max_progress != MAX_PROGRESS_NONE){
            dm_create(&progress_matrixs[model_count],5,5);
            dm_set(&progress_matrixs[model_count],0,4);
            dm_set(&progress_matrixs[model_count],0,3);
            dm_set(&progress_matrixs[model_count],1,4);
            dm_set(&progress_matrixs[model_count],1,3);
            dm_set(&progress_matrixs[model_count],2,4);
            dm_set(&progress_matrixs[model_count],2,3);
            int id=GBsetMatrix(model,"inhibit",&progress_matrixs[model_count],PINS_STRICT,PINS_INDEX_OTHER,PINS_INDEX_OTHER);
            Warning(info,"inhibit matrix registered as %d",id);
        }
    }
    
    FILE *progress = fopen("progress.txt", "w+");
    dm_print(progress, &progress_matrixs[model_count]);
    fclose(progress);

	//NOTE in older ghc: int == int64 and NOT int.
	
	int state[N];
	prcrl_get_init(context->spec,state);
    GBsetInitialState(model,state);
    
    if (internal_max_progress){
        GBsetNextStateAll(model,PRCRLgetTransitionsAll);
    }
    
    static matrix_t dm_infos[10];
    Warning(info,"spec has %d summands",nSmds);
    dm_create(&dm_infos[model_count], nSmds, state_lengths[model_count]);
    for(int i=0;i<nSmds;i++){
        for(int j=0;j<state_lengths[model_count];j++){
            if (prcrl_is_used(context->spec,i,j)){
                dm_set(&dm_infos[model_count], i, j);
            }
        }
    }
    GBsetDMInfo(model, &dm_infos[model_count]);
    GBsetNextStateLong(model,PRCRLgetTransitionsLong);
    
    //This commented out because of parallel composition
/*    model_t raw_model=GBcreateBase();
    GBcopyChunkMaps(raw_model,model);
    GBsetLTStype(raw_model,ltstype);
    GBsetContext(raw_model,context);
    GBsetInitialState(raw_model,state);
    GBsetDMInfo(raw_model, &dm_infos[model_count]);
    GBsetNextStateLong(raw_model,PRCRLgetTransitionsLong);
    context->cached=GBaddCache(raw_model);
*/
    GBsetStateLabelsAll(model,get_state_labels);
    GBsetStateLabelLong(model, get_state_label);
    GBsetStateLabelInfo(model, &sl_infos[model_count]);

    
    if (enable_rewards){
        if (reach_smds>0){
            GBsetDefaultFilter(model,SSMcreateSWPset("*_numerator;*_denominator;goal;action;group;numerator;denominator"));
        } else {
            GBsetDefaultFilter(model,SSMcreateSWPset("*_numerator;*_denominator;action;group;numerator;denominator"));
        }
    } else {
        if (reach_smds>0){
            GBsetDefaultFilter(model,SSMcreateSWPset("goal;action;group;numerator;denominator"));
        } else {
            GBsetDefaultFilter(model,SSMcreateSWPset("action;group;numerator;denominator"));
        }
    }

    if(check_confluence){
        Warning(info,"setting confluence matrix");
        HsStablePtr conf;
        conf=get_confluent_summands(context->spec);
        while(!empty_conf(conf)){
            int i=head_conf(conf);
            dm_unset(&conf_infos[model_count], 1, i); // remove confluent from silent
            dm_set(&conf_infos[model_count], 0, i);
            conf=tail_conf(conf);
        }
        GBsetMatrix(model,"confluent",&conf_infos[model_count],PINS_STRICT,PINS_INDEX_OTHER,PINS_INDEX_GROUP);
    }

	Warning(info,"model %s loaded",name);
	model_count++;
}

void prcrl_load_model(model_t model,const char*name){
    common_load_model(model,name,0);
}

void mapa_load_model(model_t model,const char*name){
    common_load_model(model,name,1);
}



