/*
 * pins2pins-parallel.c
 *
 *  Created on: 2 dec. 2014
 *      Author: sybe
 */
#include <hre/config.h>

#include <stdlib.h>

#include <hre/user.h>
#include <pins-lib/pins.h>


static int model_choice;
static int *global_source;
static TransitionCB callb;
static model_t *models;
static int model_count;
typedef matrix_t* (*matrixCall)(model_t model);


void
combineMatrices(matrixCall mc, model_t *models, matrix_t *dst){
    int columns[model_count];
    int rows[model_count];
    int columns_total = 0;
    int rows_total = 0;
    for(int i = 0; i < model_count; i++){
        columns[i]      = dm_ncols(mc(models[i]));
        rows[i]         = dm_nrows(mc(models[i]));
        columns_total   += columns[i];
        rows_total      += rows[i];
    }
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
}

//Eigen callback functie
static void parralel_cb (void*context,transition_info_t*transition_info,int*dst,int*cpy){
//    Warning(info, "Callback");
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
    callb(context, transition_info, dest, cpy);
}

int
getTransitionsLong (model_t m, int group, int *src, TransitionCB cb, void *ctx)
{
//    Warning(info, "NextState Call");
    global_source = src;
    callb = cb;
    int result;
    int groups[model_count];
    int state_vars[model_count];
    for(int i = 0; i < model_count; i++){
        groups[i] = dm_nrows(GBgetDMInfo(models[i]));
        state_vars[i] = lts_type_get_state_length (GBgetLTStype(models[i]));
    }
    int groups_counted = 0;
    int state_vars_counted = 0;
    int group_found = 0;
    for(int i = 0; i < model_count && !group_found; i++){
        if(group < groups[i] + groups_counted && group >= groups_counted){
            model_choice = i;
            int source[state_vars[i]];

            for(int j = 0; j < state_vars[i]; j++){
                source[j] = src[j + state_vars_counted];
//                Warning(info, "%d", source[j]);
            }
            result = GBgetTransitionsLong(models[i], group - groups_counted, source, parralel_cb, ctx);
            group_found = 1;
//            Warning(info, "Model:%d", i);
        }
        groups_counted += groups[i];
        state_vars_counted += state_vars[i];
    }
 //   Warning(info, "Result:%d", result);
    return result;
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
    model_count = file_count;
    models = malloc(file_count*sizeof(model_t));
    for(int i = 0; i < file_count; i++){
        Warning(info, "Creating base");
        models[i] = GBcreateBase();
        Warning(info, "Setting chunk methods");
        GBsetChunkMethods(models[i],HREgreyboxNewmap,HREglobal(),
                          HREgreyboxI2C,
                          HREgreyboxC2I,
                          HREgreyboxCAtI,
                          HREgreyboxCount);
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
            Warning(info, " %d", s0_local[j]);
        }
        len_total += len_local;
    }

    s0_total[len_total];
    GBsetInitialState(composition, s0_total);

    //Support copy
    int support = 1;
    for(int i = 0; i < model_count && support; i++){
        support = support && GBsupportsCopy(models[i]);
    }
    if(support){
        GBsetSupportsCopy(composition);
    }


//    GBinitModelDefaults(&composition, model1);
    GBsetNextStateLong(composition, getTransitionsLong);
    GBsetStateLabelLong(composition, getStateLabelLong);
    GBsetTransitionInGroup(composition, transitionInGroup);
//    GBcopyChunkMaps(composition, model1);
}

