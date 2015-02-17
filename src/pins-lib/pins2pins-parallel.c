/*
 * pins2pins-parallel.c
 *
 *  Created on: 2 dec. 2014
 *      Author: sybe
 */
#include <hre/config.h>

#include <stdlib.h>

#include <hre/user.h>
#include <ltsmin-lib/ltsmin-standard.h>
#include <pins-lib/pins.h>


static int model_choice;
static int *global_source; //TODO dit is niet een nette manier van doorgeven
static TransitionCB callb; //TODO dit is niet een nette manier van doorgeven
static model_t *models;
static int model_count;
static int* correct_groups;

static int TAU = 0;
static int RATE = 1;
static int INPUT = 2;
static int OUTPUT = 3;
static int INTERN = 4;

static int MAX_LABEL_LENGTH = 100;

typedef matrix_t* (*matrixCall)(model_t model);


void
combineMatrices(matrixCall mc, model_t *models, matrix_t *dst){
    int columns[model_count];
    int rows[model_count];
    int columns_total = 0;
    int rows_total = 0;
    int rows_product = 1;
    for(int i = 0; i < model_count; i++){
        columns[i]      = dm_ncols(mc(models[i]));
        rows[i]         = dm_nrows(mc(models[i]));
        columns_total   += columns[i];
        rows_total      += rows[i];
        rows_product    *= rows[i];
    }
     rows_total += rows_product;
     dm_create(dst, rows_total, columns_total);
     int cols_created = 0;
     int rows_created = 0;
     for(int i = 0; i < model_count; i++){
         for(int j = 0; j < rows[i]; j++){
             for(int k = 0; k < columns[i]; k++){
                 if(dm_is_set(mc(models[i]), j, k)){
                     dm_set(dst, j + rows_created, k + cols_created);
                 }
             }
         }
         cols_created += columns[i];
         rows_created += rows[i];
     }
     //Voor 2 modellen
     for(int i = 0; i < rows[0]; i++){
         for(int j = 0; j < rows[1]; j++){
             for(int k = 0; k < columns[0]; k++){
                 if(dm_is_set(mc(models[0]), i, k)){
                     dm_set(dst, j + rows_created + i * rows[1], k);
                 }
             }
         }
     }
     for(int i = 0; i < rows[1]; i++){
         for(int j = 0; j < rows[0]; j++){
             for(int k = 0; k < columns[1]; k++){
                 if(dm_is_set(mc(models[1]), i, k)){
                     dm_set(dst, i + rows_created + j * rows[1], k + columns[0]);
                 }
             }
         }
     }
}

void
create_correct_groups(model_t model, char *file1, char *file2){
    FILE *f1 = fopen(file1, "r");
    char c;
    int group = 0;
    char labels1[dm_nrows(GBgetDMInfo(models[0]))][MAX_LABEL_LENGTH];
    int types1[dm_nrows(GBgetDMInfo(models[0]))];
    while ((c = getc(f1)) != EOF){
        if(c == '='){
            char c1 = getc(f1);
            if(c1 == '>'){
                getc(f1);//Space
                char label[MAX_LABEL_LENGTH];
                fscanf(f1, "%s", label);
                strcpy(labels1[group], label);
                if (label != NULL){
                    switch(label[0]){
                    case '(' :
                        types1[group] = RATE;
                        break;
                    case 't' :
                        if (strcmp(label, "tau") == 0) {
                            types1[group] = TAU;
                        } else {
                            types1[group] = OUTPUT;
                        }
                        break;
                    default:
                        types1[group] = OUTPUT;
                        break;
                    }
                }
                group++;
            }
        }
    }
    fclose(f1);
    FILE *f2 = fopen(file2, "r");
    group = 0;
    char labels2[dm_nrows(GBgetDMInfo(models[1]))][100];
    int types2[dm_nrows(GBgetDMInfo(models[1]))];
    while ((c = getc(f2)) != EOF){
        if(c == '='){
            char c1 = getc(f2);
            if(c1 == '>'){
                getc(f2);//Space
                char label[MAX_LABEL_LENGTH];
                fscanf(f2, "%s", label);
                strcpy(labels2[group], label);
                if (label != NULL){
                   switch(label[0]){
                   case '(' :
                        types2[group] = RATE;
                        break;
                    case 't' :
                        if (strcmp(label, "tau") == 0) {
                            types2[group] = TAU;
                        } else {
                            types2[group] = OUTPUT;
                        }
                        break;
                    default:
                        types2[group] = OUTPUT;
                        break;
                    }
                }
                group++;
            }
        }
    }
    fclose(f2);
    correct_groups = RTmalloc(dm_nrows(GBgetDMInfo(model))*sizeof(int));
    for(int i = 0; i < dm_nrows(GBgetDMInfo(model)); i++){
        if(i < dm_nrows(GBgetDMInfo(models[0]))){
            if((types1[i] == TAU || types1[i] == RATE)){
                correct_groups[i] = 1;
            } else {
                correct_groups[i] = 1;
                for(int j = 0; j < dm_nrows(GBgetDMInfo(models[1])); j++){
                    if(strcmp(labels2[j], labels1[i]) == 0){
                        correct_groups[i] = 0;
                    }
                }
            }
        } else {
            if(i < dm_nrows(GBgetDMInfo(models[0]))+ dm_nrows(GBgetDMInfo(models[1]))){
                if((types2[i - dm_nrows(GBgetDMInfo(models[0]))] == TAU || types2[i - dm_nrows(GBgetDMInfo(models[0]))] == RATE)){
                    correct_groups[i] = 1;
                } else {
                    correct_groups[i] = 1;
                    for(int j = 0; j < dm_nrows(GBgetDMInfo(models[0])); j++){
                        if(strcmp(labels1[j], labels2[i - dm_nrows(GBgetDMInfo(models[0]))]) == 0){
                            correct_groups[i] = 0;
                        }
                    }
                }
            } else {
                int group_nr = i - dm_nrows(GBgetDMInfo(models[0])) - dm_nrows(GBgetDMInfo(models[1]));
                int group1 = group_nr / dm_nrows(GBgetDMInfo(models[0]));
                int group2 = group_nr % dm_nrows(GBgetDMInfo(models[0]));
                if(types1[group1] != RATE && types1[group1] != TAU && types1[group1] == types2[group2] && strcmp(labels1[group1],labels2[group2]) == 0){
                    correct_groups[i] = 1;
                } else {
                    correct_groups[i] = 0;
                }
            }
        }
    }
}

//Eigen callback functie
static void parralel_cb (void*context,transition_info_t*transition_info,int*dst,int*cpy){
    int columns[model_count];
    int columns_total = 0;
    for(int i = 0 ; i < model_count; i++){
        columns[i] = lts_type_get_state_length(GBgetLTStype(models[i]));
        columns_total += columns[i];
    }
    int dest[columns_total];
    int cols_counted = 0;
    for(int i = 0; i < model_count; i++){
        if(model_choice == i){
            for(int j = 0; j < columns[i]; j++){
                dest[j + cols_counted]=dst[j];
            }
        } else {
            for(int j = 0; j < columns[i]; j++){
                dest[j + cols_counted] = global_source[j + cols_counted];
            }
        }
        cols_counted += columns[i];
    }
    //TODO transition_info (niet voor mapa :) )
    callb(context, transition_info, dest, cpy);
}

static void parallel_sync_cb1(void*context,transition_info_t*transition_info,int*dst,int*cpy){
    int columns = lts_type_get_state_length(GBgetLTStype(models[0]));
    for(int j = 0; j < columns; j++){
        global_source[j] = dst[j];
    }
}

int
getTransitionsLong (model_t m, int group, int *src, TransitionCB cb, void *ctx)
{
    if(correct_groups[group]){
        global_source = src;
        callb = cb;
        int result;
        int groups[model_count];
        int state_vars[model_count];
        int total_groups = 0;
        for(int i = 0; i < model_count; i++){
            groups[i] = dm_nrows(GBgetDMInfo(models[i]));
            state_vars[i] = lts_type_get_state_length (GBgetLTStype(models[i]));
            total_groups += groups[i];
        }
        if (group < total_groups){
            int groups_counted = 0;
            int state_vars_counted = 0;
            int group_found = 0;
            for(int i = 0; i < model_count && !group_found; i++){
                if(group < groups[i] + groups_counted && group >= groups_counted){
                    model_choice = i;
                    int source[state_vars[i]];
                    for(int j = 0; j < state_vars[i]; j++){
                        source[j] = src[j + state_vars_counted];
                    }
                    result = GBgetTransitionsLong(models[i], group - groups_counted, source, parralel_cb, ctx);
                    group_found = 1;
                }
                groups_counted += groups[i];
                state_vars_counted += state_vars[i];
            }
        } else {
            //Synchronisatie, nu voor 2 modellen
            group -= total_groups;
            int group1 = group / groups[1];
            int group2 = group % groups[1];
            int source1[state_vars[0]];
            for(int i = 0; i < state_vars[0]; i++){
                source1[i] = src[i];
            }
            result = GBgetTransitionsLong(models[0], group1, source1, parallel_sync_cb1, ctx);
            if (result != 0){
                model_choice = 1;
                int source2[state_vars[1]];
                for(int i = 0; i < state_vars[1]; i++){
                    source2[i] = src[i + state_vars[0]];
                }
                result = GBgetTransitionsLong(models[1], group2, source2, parralel_cb, ctx);
            }
        }
        return result;
    } else {
        return 0;
    }
}

int
getStateLabelLong(model_t m, int label, int *state){
    Warning(info, "State Label call");
    int labels[model_count];
    int state_vars[model_count];
    for(int i = 0; i<model_count; i++){
        labels[i] = lts_type_get_state_label_count(GBgetLTStype(models[i]));
        state_vars[i] = lts_type_get_state_length (GBgetLTStype(models[i]));
    }
    int labels_counted = 0;
    int state_vars_counted = 0;
    int model_found = 0;
    int result;
    for(int i = 0; i < model_count && !model_found; i++){
        if(label < labels[i] + labels_counted && label >= labels_counted){
            model_found = 1;
            int local_state[state_vars[i]];
            for(int j = 0; j < state_vars[i]; j++){
                local_state[j] = state[j + state_vars_counted];
            }
            result = GBgetStateLabelLong(models[i], label - labels_counted, local_state);
        }
        labels_counted += labels[i];
        state_vars_counted += state_vars[i];
    }
    return result;
}

/*
incorrect

int
getTransitionsAll(model_t model,int*src,TransitionCB cb,void*context){
    global_source = src;
    callb = cb;
    int result = 0;
    int state_vars[model_count];
    for(int i = 0; i < model_count; i++){
        state_vars[i] = lts_type_get_state_length (GBgetLTStype(models[i]));
    }
    int state_vars_counted = 0;
    for(int i = 0; i < model_count; i++){
        model_choice = i;
        int local_source[state_vars[i]];
        for(int j = 0; j < state_vars[i]; j++){
            local_source[j] = src[state_vars_counted + j];
        }
        result += GBgetTransitionsAll(models[i], local_source, parralel_cb, context);
        state_vars_counted += state_vars[i];
    }
    return result;
}*/


//TODO uitbreiden voor synchronisatie
int
transitionInGroup(model_t m, int* labels, int group){
    int groups[model_count];
    int label_count[model_count];
    for(int i = 0; i < model_count; i++){
        groups[i] = dm_nrows(GBgetDMInfo(models[i]));
        label_count[i] = lts_type_get_edge_label_count(GBgetLTStype(models[i]));
    }
    int result = 0;
    int groups_counted = 0;
    int label_count_counted = 0;
    for(int i = 0; i < model_count; i++){
        if(group < groups[i] + groups_counted && group >= groups_counted){
            int labels_in_model[label_count[i]];
            for(int j = 0; j < label_count[i]; j++){
                labels_in_model[j] = labels[j + label_count_counted];
            }
            result = GBtransitionInGroup(models[i], labels_in_model, group - groups_counted);
        }
        groups_counted += groups[i];
        label_count_counted += label_count[i];
    }
    return result;
}

int
matrices_present(matrixCall mc, model_t *models){
    int result = 1;
    for(int i = 0; i < model_count; i++){
        result = result && (mc(models[i]) != NULL);
    }
    return result;
}

void
GBparallelCompose (model_t composition, char **files, int file_count, pins_loader_t loader)
{
    Warning(info, "Initializing awesome parallel composition layer");
    model_count = 2;//file_count
    models = malloc(model_count*sizeof(model_t));
    for(int i = 0; i < 2; i++){
        Warning(info, "Creating base");
        models[i] = GBcreateBase();
        Warning(info, "Setting chunk methods");
        GBsetChunkMethods(models[i],HREgreyboxNewmap,HREglobal(),
                          HREgreyboxI2C,
                          HREgreyboxC2I,
                          HREgreyboxCAtI,
                          HREgreyboxCount);
        GBsetModelNr(models[i], i);
        Warning(info, "Starting loader");
        loader(models[i], files[i]);
        Warning(info, "Loader finished");
    }
    Warning(info, "Models to compose:%d",file_count);


    matrix_t *p_dm              = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_read         = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_may_write    = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_must_write   = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_expand       = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_project      = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_state_label  = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_commute      = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_NDS          = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_NES          = RTmalloc(sizeof(matrix_t));

    if(matrices_present(GBgetDMInfo, models)){
        combineMatrices(GBgetDMInfo, models, p_dm);
        GBsetDMInfo(composition, p_dm);
    }
    if(matrices_present(GBgetDMInfoRead, models)){
        combineMatrices(GBgetDMInfoRead, models, p_dm_read);
        GBsetDMInfoRead(composition, p_dm_read);
    }
    if(matrices_present(GBgetDMInfoMayWrite, models)){
        combineMatrices(GBgetDMInfoMayWrite, models, p_dm_may_write);
        GBsetDMInfoMayWrite(composition, p_dm_may_write);
    }
    if(matrices_present(GBgetDMInfoMustWrite, models)){
        combineMatrices(GBgetDMInfoMustWrite, models, p_dm_must_write);
        GBsetDMInfoMustWrite(composition, p_dm_must_write);
    }
    if(matrices_present(GBgetExpandMatrix, models)){
        combineMatrices(GBgetExpandMatrix, models, p_dm_expand);
        GBsetExpandMatrix(composition, p_dm_expand);
    }
    if(matrices_present(GBgetProjectMatrix, models)){
        combineMatrices(GBgetProjectMatrix, models, p_dm_project);
        GBsetProjectMatrix(composition, p_dm_project);
    }
    if(matrices_present(GBgetDoNotAccordInfo, models)){
        combineMatrices(GBgetDoNotAccordInfo, models, p_dm_project);
        GBsetDoNotAccordInfo(composition, p_dm_project);
    }
    if(matrices_present(GBgetStateLabelInfo, models)){
        combineMatrices(GBgetStateLabelInfo, models, p_dm_state_label);
        GBsetStateLabelInfo(composition, p_dm_state_label);
    }
    if(matrices_present(GBgetCommutesInfo, models)){
        combineMatrices(GBgetCommutesInfo, models, p_dm_commute);
        GBsetCommutesInfo(composition, p_dm_commute);
    }
    if(matrices_present(GBgetGuardNDSInfo, models)){
        combineMatrices(GBgetGuardNDSInfo, models, p_dm_NDS);
        GBsetGuardNDSInfo(composition, p_dm_NDS);
    }
    if(matrices_present(GBgetGuardNESInfo, models)){
        combineMatrices(GBgetGuardNESInfo, models, p_dm_NES);
        GBsetGuardNESInfo(composition, p_dm_NES);
    }
    //Mapa specific

    create_correct_groups(composition, files[2], files[3]);


    //GBsetMatrix
    //Class matrix
    int id[model_count];
    int rows_class[model_count];
    int columns_class[model_count];
    int tot_rows_class = 0;
    int tot_columns_class = 0;
    int product_columns_class = 1;
    int class_matrix_needed = 1;
    for(int i = 0; i < model_count; i++){
        id[i] = GBgetMatrixID(models[i],LTSMIN_EDGE_TYPE_ACTION_CLASS);
        if (id[i] >= 0){
            rows_class[i] = dm_nrows(GBgetMatrix(models[i], id[i]));
            columns_class[i] = dm_ncols(GBgetMatrix(models[i], id[i]));
            tot_rows_class += rows_class[i];
            tot_columns_class += columns_class[i];
            product_columns_class *= columns_class[i];
        } else {
            class_matrix_needed = 0;
        }
    }
    tot_columns_class += product_columns_class;
    if(class_matrix_needed){
        static matrix_t p_dm_class;//          = RTmalloc(sizeof(matrix_t));
        dm_create(&p_dm_class, rows_class[0], tot_columns_class);
        int class_columns_counted = 0;
        for(int i = 0; i < model_count; i++){
            for(int j = 0; j < rows_class[i]; j++){
                for(int k = 0; k <columns_class[i]; k++){
                    if(dm_is_set(GBgetMatrix(models[i], id[i]), j, k)){
                        dm_set(&p_dm_class, j, k + class_columns_counted);
                    }
                }
            }
            class_columns_counted += columns_class[i];
        }
        //voor 2 modellen
        for(int i = 0; i < columns_class[0]; i++){
            for(int j = 0; j < columns_class[1]; j++){
                for(int k = 0; k < rows_class[0]; k++){
                    if(dm_is_set(GBgetMatrix(models[0], id[0]), k, i) && dm_is_set(GBgetMatrix(models[1], id[1]), k, j)){
                        dm_set(&p_dm_class, k, class_columns_counted + i * columns_class[1] + j);
                    }
                }

            }
        }
/*
        FILE *original = fopen("original.txt", "w+");
        FILE *composition = fopen("composition.txt", "w+");
        dm_print(original, GBgetMatrix(models[0], id[0]));
        dm_print(composition, &p_dm_class);
        fclose(original);
        fclose(composition);
*/
        GBsetMatrix(composition,LTSMIN_EDGE_TYPE_ACTION_CLASS,&p_dm_class,PINS_STRICT,PINS_INDEX_OTHER,PINS_INDEX_GROUP);
    }
    //Inhibit matrix
    int inhibit_id = GBgetMatrixID(models[0], "inhibit");
    if(inhibit_id >= 0){
        static matrix_t p_dm_inhibit ;//         = RTmalloc(sizeof(matrix_t));
        dm_create(&p_dm_inhibit, 3, 3);
        for(int i = 0; i < 3; i ++){
            for(int j = 0; j < 3; j++){
                if(dm_is_set(GBgetMatrix(models[0], inhibit_id), i, j)){
                    dm_set(&p_dm_inhibit, i, j);
                }
            }
        }

        GBsetMatrix(composition,"inhibit",&p_dm_inhibit,PINS_STRICT,PINS_INDEX_OTHER,PINS_INDEX_OTHER);
    }
    //LTS Type
    lts_type_t ltstype = lts_type_create();

    int state_length = 0;
    int state_label_count = 0;
    int edge_label_count = 0;
    for (int i = 0; i < model_count; i++){
        state_length += lts_type_get_state_length (GBgetLTStype(models[i]));
        state_label_count += lts_type_get_state_label_count (GBgetLTStype(models[i]));
        edge_label_count += lts_type_get_edge_label_count (GBgetLTStype(models[i]));
    }
    lts_type_set_state_length(ltstype, state_length);
    lts_type_set_state_label_count(ltstype, state_label_count);
    lts_type_set_edge_label_count(ltstype, edge_label_count);

    int state_length_counted = 0;
    int edge_labels_counted = 0;
    int state_labels_counted = 0;
    for (int i = 0; i < model_count; i++){
        for (int j = 0; j < lts_type_get_state_length (GBgetLTStype(models[i])); j++){
            lts_type_set_state_name(ltstype, j + state_length_counted, lts_type_get_state_name(GBgetLTStype(models[i]), j));
            lts_type_set_state_type(ltstype, j + state_length_counted, lts_type_get_state_type(GBgetLTStype(models[i]), j));
            lts_type_set_state_typeno(ltstype, j + state_length_counted, lts_type_get_state_typeno(GBgetLTStype(models[i]), j));
        }
        for (int j = 0; j < lts_type_get_edge_label_count (GBgetLTStype(models[i])); j++){
            lts_type_set_edge_label_name(ltstype, j + edge_labels_counted, lts_type_get_edge_label_name(GBgetLTStype(models[i]), j));
            lts_type_set_edge_label_type(ltstype, j + edge_labels_counted, lts_type_get_edge_label_type(GBgetLTStype(models[i]), j));
            lts_type_set_edge_label_typeno(ltstype, j + edge_labels_counted, lts_type_get_edge_label_typeno(GBgetLTStype(models[i]), j));
        }
        for (int j = 0; j < lts_type_get_state_label_count (GBgetLTStype(models[i])); j++){
            lts_type_set_state_label_name(ltstype, j + state_labels_counted, lts_type_get_state_label_name(GBgetLTStype(models[i]), j));
            lts_type_set_state_label_type(ltstype, j + state_labels_counted, lts_type_get_state_label_type(GBgetLTStype(models[i]), j));
            lts_type_set_state_label_typeno(ltstype, j + state_labels_counted, lts_type_get_state_label_typeno(GBgetLTStype(models[i]), j));
        }
        state_length_counted += lts_type_get_state_length (GBgetLTStype(models[i]));
        edge_labels_counted += lts_type_get_edge_label_count(GBgetLTStype(models[i]));
        state_labels_counted += lts_type_get_state_label_count(GBgetLTStype(models[i]));
    }

    GBsetLTStype(composition, ltstype);

    int len_total = 0;
    int s0_total[lts_type_get_state_length(ltstype)];
    for (int i = 0; i < model_count; i++){
        lts_type_get_state_length (GBgetLTStype(models[i]));
        int len_local = lts_type_get_state_length (GBgetLTStype(models[i]));
        int s0_local[len_local];
        GBgetInitialState(models[i], s0_local);
        for(int j = 0; j < len_local; j++){
            s0_total[j + len_total] = s0_local[j];
        }
        len_total += len_local;
    }

    GBsetInitialState(composition, s0_total);

    //Support copy
    int support_copy = 1;
    for(int i = 0; i < model_count && support_copy; i++){
        support_copy = support_copy && GBsupportsCopy(models[i]);
    }
    if(support_copy){
        GBsetSupportsCopy(composition);
    }

//    GBsetNextStateAll(composition, getTransitionsAll); function is still incorrect
    GBsetNextStateLong(composition, getTransitionsLong);
    GBsetStateLabelLong(composition, getStateLabelLong);
    GBsetTransitionInGroup(composition, transitionInGroup);
}

