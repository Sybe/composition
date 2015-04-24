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


static model_t *models;     //Array of models to be composed
static int model_count;     //Number of models to be composed
static int* correct_groups; //Array of 0 and 1, 1 if the group should be evaluated
static int bool_type;       //Boolean type

static int iomapa = 0;

static int TAU;
static int INTERN;
static int OUTPUT;
static int INPUT;
static int RATE;

#define MAX_LABEL_LENGTH 100

typedef matrix_t* (*matrixCall)(model_t model);

static model_t* model_comp;

typedef struct{
    void *ctx;       //Original Context
    int  *state;     //A state
    int model_nr;    //The number of the model, equal to the position in the models array
    TransitionCB cb; //The original callback function
    int group;       //The transition group
    int sync;        //True if it is a synchronizing transition
    int group1;      //The original transition group from the first model
    int group2;      //The original transition group from the second model
    model_t model;   //The composed model
    char* label;     //The label of the action
    int result;      //If synchronization succeeds this is set to 1, else to 0
} parrallel_ctx ;

typedef struct{
    int **map;
    int *length;
    int *maxLength;
} mapping_t;         //Mapping for the action chunks

static mapping_t* map;


/**
 * Strips the '!' or '?' from the label and any variables after that character
 * Needed to check if a input and output action can synchronize
 * Only useful when the variable is not set to a value yet
 */
void
strip_io_label_complete(char* label){
    for(int i = 0; i < MAX_LABEL_LENGTH && label[i] != '\0'; i++){
        if(label[i] == '?' || label[i] == '!'){
            while(label[i] != '\0'){
                label[i] = '\0';
                i++;
            }
        }
    }
}
/**
 * Strips the '!' or '?' from the label
 * Needed to check if a input and output action can synchronize
 */
void
strip_io_label(char* label){
    for(int i = 0; i < MAX_LABEL_LENGTH && label[i] != '\0'; i++){
        if(label[i] == '?' || label[i] == '!'){
            i++;
            while(label[i - 1] != '\0'){
                label[i - 1] = label[i];
                i++;
            }
        }
    }
}

void
strip_label(char* label){
    for(int i = 1; i < MAX_LABEL_LENGTH && label[i] != '\0'; i++){
        if(label[i] == '('){
            while(label[i] != '\0'){
                label[i] = '\0';
                i++;
            }
        }
    }
}

/**
 * Sets a mapping for the action chunks
 */
static void
map_chunk(int model, int from, int to){
    if(from >= map->length[model]){
        if(map->length[model] == map->maxLength[model]){
            int t[2*map->length[model]];
            for(int i = 0; i < map->length[model]; i++){
                t[i] = map->map[model][i];
            }
            map->maxLength[model] = map->maxLength[model] * 2;
            free(map->map[model]);
            map->map[model] = t;
            map->length[model] = map->length[model] + 1;
        }
    }
    map->map[model][from] = to;
}

/**
 * Returns the mapping for the action chunks
 */
static int
get_chunk(int model, int from){
    return map->map[model][from];
}


// Mapa specific
void
set_chunks(model_t model){
    int chunks_counted[lts_type_get_type_count(GBgetLTStype(model))];
    int state_vars_counted = 0;
    int offset = 0;
    int bools_counted = 0;
    int total_bools = 0;
    int bools[2];
    for (int i = 0; i < lts_type_get_type_count(GBgetLTStype(model)); i++){
        chunks_counted[i] = 0;
    }
    //Dit specifiek voor states labels
    for(int i = 0; i < model_count; i++){
        int j;
        for(j = 0; j < lts_type_get_state_length(GBgetLTStype(models[i])) && strcmp(lts_type_get_state_type(GBgetLTStype(models[i]), j), "Bool") != 0; j++){
            if(strcmp(lts_type_get_state_type(GBgetLTStype(models[i]), j), "Bool") != 0){
                for(int k = 0; k < GBchunkCount(models[i], j + 1 - bools_counted); k++){
                    chunk c = GBchunkGet(models[i], j + 1 - bools_counted, k);
                    GBchunkPutAt(model, j + state_vars_counted + 1 - bools_counted, c, k);
                }
            } else {
                bools_counted++;
            }
        }
        state_vars_counted += j - bools_counted;
        total_bools += bools_counted;
        bools[i] = bools_counted;
        bools_counted = 0;
    }
}

/*
 * Combines two matrices into one matrix in the following order(each number is a row):
 *  /-\     /-\     /---\
 *  |1|     |4|     |1|0|
 *  |2|  *  |5| ->  |2|0|
 *  |3|     \-/     |3|0|
 *  \-/             |0|4|
 *                  |0|5|
 *                  |1|4|
 *                  |1|5|
 *                  |2|4|
 *                  |2|5|
 *                  |3|4|
 *                  |3|5|
 *                  \---/
 */
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

/**
 * Combines the State Label matrices of multiple models
 */
void combineSLMatrices(model_t *models, matrix_t *dst){
    int columns[model_count];
    int rows = dm_nrows(GBgetStateLabelInfo(models[0]));
    int columns_total = 0;
    for(int i = 0; i < model_count; i++){
        columns[i]      = dm_ncols(GBgetStateLabelInfo(models[i]));
        columns_total   += columns[i];
    }
    int columns_created = 0;
    dm_create(dst, rows, columns_total);
    for(int i = 0; i < model_count; i++){
        for(int j = 0; j < columns[i]; j++){
            for(int k = 0; k < rows; k++){
                if(dm_is_set(GBgetStateLabelInfo(models[i]), k, j)){
                    dm_set(dst, k, j + columns_created);
                }
            }
        }
        columns_created += columns[i];
    }
}
/*
 * Reads the input txt files in mlppe format and based on those
 * creates an array which decides what groups to evaluate
 */
// MAPA specific
void
create_correct_io_groups(model_t model, char **files, int file_count){

    int max_groups = 0;
    for (int i = 0; i < file_count; i++){
        if(dm_nrows(GBgetDMInfo(models[i])) > max_groups){
            max_groups = dm_nrows(GBgetDMInfo(models[i]));
        }
    }
    char labels[file_count][max_groups][MAX_LABEL_LENGTH];
    int types[file_count][max_groups];

    for(int i = 0; i < file_count; i++){
        FILE *f = fopen(files[i], "r");
        char c;
        int group = 0;
        while ((c = getc(f)) != EOF){
            if(c == '='){
                char c1 = getc(f);
                if(c1 == '>'){
                    getc(f);//Space
                    char label[MAX_LABEL_LENGTH];
                    HREassert(fscanf(f, "%s", label) == 1);
                    strcpy(labels[i][group], label);
                    if (label != NULL){
                        switch(label[0]){
                        case '(' :
                            types[i][group] = RATE;
                            break;
                        default :
                            if (strcmp(label, "tau") == 0) {
                                types[i][group] = TAU;
                            } else {
                                if(strchr(label,  '?') != NULL){
                                    types[i][group] = INPUT;
                                } else {
                                    if(strchr(label,  '!') != NULL){
                                        types[i][group] = OUTPUT;
                                    } else {
                                        types[i][group] = INTERN;
                                    }
                                }
                            }
                            break;
                        }
                    }
                    group++;
                }
            }
        }
    }
    Warning(info, "files closed");
    correct_groups = RTmalloc(dm_nrows(GBgetDMInfo(model))*sizeof(int));
    for(int i = 0; i < dm_nrows(GBgetDMInfo(model)); i++){
        if(i < dm_nrows(GBgetDMInfo(models[0]))){//Row in model 1
            if((types[0][i] == TAU || types[0][i] == RATE || types[0][i] == INTERN)){
                correct_groups[i] = 1;//Never need to synchronize, so always execute
            } else { //input or output
                correct_groups[i] = 1;
                char label1[MAX_LABEL_LENGTH];
                strcpy(label1, labels[0][i]);
                strip_io_label_complete(label1);
                for(int j = 0; j < dm_nrows(GBgetDMInfo(models[1])); j++){
                    char label2[MAX_LABEL_LENGTH];
                    strcpy(label2, labels[1][j]);
                    strip_io_label_complete(label2);//Strip the '?' or '!'
                    if(strcmp(label2, label1) == 0 //If it is the same action
                        && ((types[0][i] == INPUT  && types[1][j] == OUTPUT) //And one action is input and the other output
                          ||(types[0][i] == OUTPUT && types[1][j] == INPUT))){
                        correct_groups[i] = 0; //Then it should synchronize, so not act alone
                    }
                }
            }
        } else {
            if(i < dm_nrows(GBgetDMInfo(models[0]))+ dm_nrows(GBgetDMInfo(models[1]))){//Row in model 2
                if((types[1][i - dm_nrows(GBgetDMInfo(models[0]))] == TAU
                 || types[1][i - dm_nrows(GBgetDMInfo(models[0]))] == RATE
                 || types[1][i - dm_nrows(GBgetDMInfo(models[0]))] == INTERN)){
                    correct_groups[i] = 1;//Never need to synchronize, so always execute
                } else { //input or output
                    correct_groups[i] = 1;
                    char label2[MAX_LABEL_LENGTH];
                    strcpy(label2, labels[1][i  - dm_nrows(GBgetDMInfo(models[0]))]);
                    strip_io_label_complete(label2);//Strip the '?' or '!'
                    for(int j = 0; j < dm_nrows(GBgetDMInfo(models[0])); j++){
                        char label1[MAX_LABEL_LENGTH];
                        strcpy(label1, labels[0][j]);
                        strip_io_label_complete(label1);//Strip the '?' or '!'
                        if(strcmp(label1, label2) == 0 //If it is the same action
                            && ((types[1][i - dm_nrows(GBgetDMInfo(models[0]))] == INPUT  && types[0][j] == OUTPUT) //And one action is input and the other output
                              ||(types[1][i - dm_nrows(GBgetDMInfo(models[0]))] == OUTPUT && types[0][j] == INPUT))){
                            correct_groups[i] = 0;//Then it should synchronize, so not act alone
                        }
                    }
                }
            } else {//Row combined of 2 models, synchronization
                int group_nr = i - dm_nrows(GBgetDMInfo(models[0])) - dm_nrows(GBgetDMInfo(models[1]));//Restart counting at first combined row
                int group1 = group_nr / dm_nrows(GBgetDMInfo(models[1]));//Group of first model
                int group2 = group_nr % dm_nrows(GBgetDMInfo(models[1]));//Group of second model
                char label1[MAX_LABEL_LENGTH];
                char label2[MAX_LABEL_LENGTH];
                strcpy(label1, labels[0][group1]);
                strcpy(label2, labels[1][group2]);
                strip_io_label_complete(label1);//Strip the '?' or '!'
                strip_io_label_complete(label2);//Strip the '?' or '!'
                if(types[0][group1] != RATE && types[0][group1] != TAU && types[0][group1] != INTERN && strcmp(label1, label2) == 0){
                    if(types[0][group1] == INPUT && types[1][group2] == INPUT){
                        correct_groups[i] = 1;
                    } else {
                        if((types[0][group1] == INPUT  && types[1][group2] == OUTPUT)
                        || (types[0][group1] == OUTPUT && types[1][group2] == INPUT)){//Synchronization based on input vs. output possible
                            correct_groups[i] = 1;
                        } else {
                            if(types[0][group1] == OUTPUT && types[1][group2] == OUTPUT && (labels[0][group1][strlen(labels[0][group1]) - 1] == '?' || labels[0][group1][strlen(labels[0][group1]) - 1] == '!')){
                                Abort("Shared output action %s!, behavior not defined.", label1);
                            } else {
                                correct_groups[i] = 0;
                            }
                        }
                    }
                } else {
                    correct_groups[i] = 0;
                }
            }
        }
    }
    for(int i = 0; i < dm_nrows(GBgetDMInfo(model)); i++){
        printf("%d", correct_groups[i]);
    }
    printf("\n");
}

/*
 * Reads the input txt files in mlppe format and based on those
 * creates an array which decides what groups to evaluate
 */
// MAPA specific
void
create_correct_groups(model_t model, char **files, int file_count){

    int max_groups = 0;
    for (int i = 0; i < file_count; i++){
        if(dm_nrows(GBgetDMInfo(models[i])) > max_groups){
            max_groups = dm_nrows(GBgetDMInfo(models[i]));
        }
    }
    char labels[file_count][max_groups][MAX_LABEL_LENGTH];
    int types[file_count][max_groups];
    for(int i = 0; i < file_count; i++){
        Warning(info, "File nr %d", i);
        FILE *f = fopen(files[i], "r");
        char c;
        int group = 0;
        while ((c = getc(f)) != EOF){
            if(c == '='){
                char c1 = getc(f);
                if(c1 == '>'){
                    getc(f);//Space
                    char label[MAX_LABEL_LENGTH];
                    HREassert(fscanf(f, "%s", label) == 1);
                    Warning(info, "label found: %s", label);
                    strcpy(labels[i][group], label);
                    if (label != NULL){
                        switch(label[0]){
                        case '(' :
                            types[i][group] = RATE;
                            break;
                        default :
                            if (strcmp(label, "tau") == 0) {
                                types[i][group] = TAU;
                            } else {
                                types[i][group] = INTERN;
                            }
                            break;
                        }
                    }
                    group++;
                }
            }
        }
        fclose(f);
    }
    Warning(info, "files closed");
    correct_groups = RTmalloc(dm_nrows(GBgetDMInfo(model))*sizeof(int));
    for(int i = 0; i < dm_nrows(GBgetDMInfo(model)); i++){
        if(i < dm_nrows(GBgetDMInfo(models[0]))){//Row in model 1
            if((types[0][i] == TAU || types[0][i] == RATE)){
                correct_groups[i] = 1;//Never need to synchronize, so always execute
            } else { //intern
                correct_groups[i] = 1;
                char label1[MAX_LABEL_LENGTH];
                strcpy(label1, labels[0][i]);
                strip_label(label1);
                for(int j = 0; j < dm_nrows(GBgetDMInfo(models[1])); j++){
                    char label2[MAX_LABEL_LENGTH];
                    strcpy(label2, labels[1][j]);
                    strip_label(label2);
                    if(strcmp(label2, label1) == 0){ //If it is the same action
                        correct_groups[i] = 0; //Then it should synchronize, so not act alone
                    }
                }
            }
        } else {
            if(i < dm_nrows(GBgetDMInfo(models[0]))+ dm_nrows(GBgetDMInfo(models[1]))){//Row in model 2
                if((types[1][i - dm_nrows(GBgetDMInfo(models[0]))] == TAU
                 || types[1][i - dm_nrows(GBgetDMInfo(models[0]))] == RATE)){
                    correct_groups[i] = 1;//Never need to synchronize, so always execute
                } else { //input or output
                    correct_groups[i] = 1;
                    char label2[MAX_LABEL_LENGTH];
                    strcpy(label2, labels[1][i  - dm_nrows(GBgetDMInfo(models[0]))]);
                    strip_label(label2);
                    for(int j = 0; j < dm_nrows(GBgetDMInfo(models[0])); j++){
                        char label1[MAX_LABEL_LENGTH];
                        strcpy(label1, labels[0][j]);
                        strip_label(label1);
                        if(strcmp(label1, label2) == 0){ //If it is the same action
                            correct_groups[i] = 0;//Then it should synchronize, so not act alone
                        }
                    }
                }
            } else {//Row combined of 2 models, synchronization
                int group_nr = i - dm_nrows(GBgetDMInfo(models[0])) - dm_nrows(GBgetDMInfo(models[1]));//Restart counting at first combined row
                int group1 = group_nr / dm_nrows(GBgetDMInfo(models[1]));//Group of first model
                int group2 = group_nr % dm_nrows(GBgetDMInfo(models[1]));//Group of second model
                char label1[MAX_LABEL_LENGTH];
                char label2[MAX_LABEL_LENGTH];
                strcpy(label1, labels[0][group1]);
                strcpy(label2, labels[1][group2]);
                strip_label(label1);
                strip_label(label2);
                if(types[0][group1] == INTERN && types[1][group2] == INTERN && strcmp(label1, label2) == 0){
                    correct_groups[i] = 1;
                } else {
                    correct_groups[i] = 0;
                }
            }
        }
    }
    for(int i = 0; i < dm_nrows(GBgetDMInfo(model)); i++){
        printf("%d", correct_groups[i]);
    }
    printf("\n");
}


/**
 * Basic callback function that also returns to the original callback function.
 * Used for non synchronizing groups and output groups
 */
static void parralel_cb (void*context,transition_info_t*transition_info,int*dst,int*cpy){
    parrallel_ctx*ctx = (parrallel_ctx*) context;
    int columns[model_count];
    int columns_total = 0;
    for(int i = 0 ; i < model_count; i++){
        columns[i] = lts_type_get_state_length(GBgetLTStype(models[i]));
        columns_total += columns[i];
    }
    int dest[columns_total];
    int cols_counted = 0;
    for(int i = 0; i < model_count; i++){
        if(ctx->model_nr == i){
            for(int j = 0; j < columns[i]; j++){
                dest[j + cols_counted]=dst[j];
            }
        } else {
            for(int j = 0; j < columns[i]; j++){
                dest[j + cols_counted] = ctx->state[j + cols_counted];
            }
        }
        cols_counted += columns[i];
    }
    transition_info_t ti = GB_TI(transition_info->labels, ctx->group);
    ti.labels[3] = ctx->group;
    int actions = 0;
    for (int i = 0; i < lts_type_get_type_count(GBgetLTStype(ctx->model)); i++){
        if(strcmp(lts_type_get_type(GBgetLTStype(ctx->model), i),"action") == 0){
            actions = i;
        }
    }
    int old_actions = 0;
    for (int i = 0; i < lts_type_get_type_count(GBgetLTStype(models[ctx->model_nr])); i++){
        if(strcmp(lts_type_get_type(GBgetLTStype(models[ctx->model_nr]), i),"action") == 0){
            old_actions = i;
        }
    }
    chunk c = GBchunkGet(models[ctx->model_nr], old_actions, ti.labels[2]);
    if(ctx->sync){
        char* label = malloc(MAX_LABEL_LENGTH * sizeof(char));
        strcpy(label, c.data);
        if(iomapa){
            strip_io_label(label);
        } else {
            strip_label(label);
        }
        if(strcmp(label, ctx->label) == 0){
            int pos = GBchunkPut(ctx->model, actions, c);
            map_chunk(ctx->model_nr, ti.labels[2], pos);
            //Mapa specific
            ti.labels[2] = get_chunk(ctx->model_nr, ti.labels[2]);
            ctx->cb(ctx->ctx, &ti, dest, cpy);
            ctx->result = 1;
        } else {
            ctx->result = 0;
        }
    } else {
        int pos = GBchunkPut(ctx->model, actions, c);
        map_chunk(ctx->model_nr, ti.labels[2], pos);
        //Mapa specific
        ti.labels[2] = get_chunk(ctx->model_nr, ti.labels[2]);
        ctx->cb(ctx->ctx, &ti, dest, cpy);
        ctx->result = 1;
    }
}
/*
 * Used as callback function if the group in the first model is the input action, or for non-io
 */
static void parallel_sync_cb1(void*context,transition_info_t*transition_info,int*dst,int*cpy){
    parrallel_ctx*ctx = (parrallel_ctx*)context;
    int actions = 0;
    for (int i = 0; i < lts_type_get_type_count(GBgetLTStype(models[ctx->model_nr])); i++){
        if(strcmp(lts_type_get_type(GBgetLTStype(models[ctx->model_nr]), i),"action") == 0){
            actions = i;
        }
    }
    chunk c = GBchunkGet(models[ctx->model_nr], actions, transition_info->labels[2]);
    char* label=malloc(MAX_LABEL_LENGTH * sizeof(char));
    strcpy(label, c.data);
    if(iomapa){
        strip_io_label(label);
    } else {
        strip_label(label);
    }
    static char ctxLabel[MAX_LABEL_LENGTH];
    ctx->label = ctxLabel;
    strcpy(ctx->label, label);
    free(label);
    int columns = lts_type_get_state_length(GBgetLTStype(models[0]));
    for(int j = 0; j < columns; j++){
        ctx->state[j] = dst[j];
    }
}

/*
 * Used as callback function if the group in the second model is the input action
 */
static void parallel_sync_cb2(void*context,transition_info_t*transition_info,int*dst,int*cpy){
    parrallel_ctx*ctx = (parrallel_ctx*)context;
    int actions = 0;
    for (int i = 0; i < lts_type_get_type_count(GBgetLTStype(models[ctx->model_nr])); i++){
        if(strcmp(lts_type_get_type(GBgetLTStype(models[ctx->model_nr]), i),"action") == 0){
            actions = i;
        }
    }
    chunk c = GBchunkGet(models[ctx->model_nr], actions, transition_info->labels[2]);
    char* label=malloc(MAX_LABEL_LENGTH * sizeof(char));
    strcpy(label, c.data);
    strip_io_label(label);
    static char ctxLabel[MAX_LABEL_LENGTH];
    ctx->label = ctxLabel;
    strcpy(ctx->label, label);
    free(label);
    int columns = lts_type_get_state_length(GBgetLTStype(models[1]));
    int columns_model_1 = lts_type_get_state_length(GBgetLTStype(models[0]));
    for(int j = 0; j < columns; j++){
        ctx->state[j + columns_model_1] = dst[j];
    }
}

/*
 * Next state function
 */
// Mapa specific
int
getTransitionsLong (model_t m, int group, int *src, TransitionCB cb, void *ctx)
{
    if(correct_groups[group]){
        parrallel_ctx *context = malloc(sizeof(parrallel_ctx));
        context->ctx = ctx;
        context->state = src;
        context->cb = cb;
        context->group = group;
        context->sync = 0;
        context->model = m;
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
                    context->model_nr = i;
                    int source[state_vars[i]];
                    for(int j = 0; j < state_vars[i]; j++){
                        source[j] = src[j + state_vars_counted];
                    }
                    result = GBgetTransitionsLong(models[i], group - groups_counted, source, parralel_cb, context);
                    group_found = 1;
                }
                groups_counted += groups[i];
                state_vars_counted += state_vars[i];
            }
        } else {
            //Synchronisatie, nu voor 2 modellen
            context->sync = 1;
            group -= total_groups;
            int group1 = group / groups[1];
            int group2 = group % groups[1];
            context->group1 = group1;
            context->group2 = group2;
            if(iomapa){
                if(dm_is_set(GBgetMatrix(models[0], GBgetMatrixID(models[0],LTSMIN_EDGE_TYPE_ACTION_CLASS)), OUTPUT, group1)){
                    int source2[state_vars[1]];
                    for(int i = 0; i < state_vars[1]; i++){
                        source2[i] = src[i + state_vars[0]];
                    }
                    context->model_nr = 1;
                    result = GBgetTransitionsLong(models[1], group2, source2, parallel_sync_cb2, context);
                    if (result != 0){
                        context->model_nr = 0;
                        int source1[state_vars[0]];
                        for(int i = 0; i < state_vars[0]; i++){
                            source1[i] = src[i];
                        }
                        result = GBgetTransitionsLong(models[0], group1, source1, parralel_cb, context);
                    }
                } else {
                    int source1[state_vars[0]];
                    for(int i = 0; i < state_vars[0]; i++){
                        source1[i] = src[i];
                    }
                    context->model_nr = 0;
                    result = GBgetTransitionsLong(models[0], group1, source1, parallel_sync_cb1, context);
                    if (result != 0){
                        context->model_nr = 1;
                        int source2[state_vars[1]];
                        for(int i = 0; i < state_vars[1]; i++){
                            source2[i] = src[i + state_vars[0]];
                        }
                        result = GBgetTransitionsLong(models[1], group2, source2, parralel_cb, context);
                    }
                }
            } else {
                int source1[state_vars[0]];
                for(int i = 0; i < state_vars[0]; i++){
                    source1[i] = src[i];
                }
                context->model_nr = 0;
                result = GBgetTransitionsLong(models[0], group1, source1, parallel_sync_cb1, context);
                if (result != 0){
                    context->model_nr = 1;
                    int source2[state_vars[1]];
                    for(int i = 0; i < state_vars[1]; i++){
                        source2[i] = src[i + state_vars[0]];
                    }
                    result = GBgetTransitionsLong(models[1], group2, source2, parralel_cb, context);
                }
            }
        }
        free(context);
        return result;
    } else {
        return 0;
    }
}

/**
 * Implementation for GBgetStateLabelLong
 */
int
getStateLabelLong(model_t m, int label, int *state){
    int labels[model_count];
    int state_vars[model_count];
    for(int i = 0; i<model_count; i++){
        labels[i] = lts_type_get_state_label_count(GBgetLTStype(models[i]));
        state_vars[i] = lts_type_get_state_length (GBgetLTStype(models[i]));
    }
    int labels_counted = 0;
    int state_vars_counted = 0;
    int model_found = 0;
    int result = 0;
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
 * Implementation for GBtransitionInGroup
 */
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
    if(group < groups[0]){
        int labels_in_model[label_count[0]];
        for(int j = 0; j < label_count[0]; j++){
            labels_in_model[j] = labels[j + label_count_counted];
        }
        result = GBtransitionInGroup(models[0], labels_in_model, group - groups_counted);
    } else {
        if(group < groups[1]){
            int labels_in_model[label_count[1]];
            for(int j = 0; j < label_count[1]; j++){
                labels_in_model[j] = labels[j + label_count_counted];
            }
            result = GBtransitionInGroup(models[1], labels_in_model, group - groups_counted);
        } else {
            group = group - groups[0] - groups[1];
            int group1 = group / groups[1];
            int group2 = group % groups[1];
            int labels_in_model1[label_count[0]];
            for(int j = 0; j < label_count[0]; j++){
                labels_in_model1[j] = labels[j + label_count_counted];
            }
            int labels_in_model2[label_count[1]];
            for(int j = 0; j < label_count[1]; j++){
                labels_in_model2[j] = labels[j + label_count_counted];
            }
            result = GBtransitionInGroup(models[0], labels_in_model1, group1) && GBtransitionInGroup(models[1], labels_in_model2, group2);
        }
    }
    return result;
}

/*
 * Checks if all models have the matrix called by mc
 */
int
matrices_present(matrixCall mc, model_t *models){
    int result = 1;
    for(int i = 0; i < model_count; i++){
        result = result && (mc(models[i]) != NULL);
    }
    return result;
}

//Mapa specific
void
GBparallelCompose (model_t composition, char **files, int file_count, pins_loader_t loader)
{
    if(iomapa){
        TAU = 0;
        INTERN = 1;
        OUTPUT = 2;
        INPUT = 3;
        RATE = 4;
    } else {
        TAU = 0;
        INTERN = 1;
        RATE = 2;
    }
    Warning(info, "Initializing awesome parallel composition layer");
    model_count = file_count / 2;//file_count

    if(file_count < 4){
        Abort("Trying to compose with only %d input files, at least 4 needed", file_count);
    }
    models = malloc(model_count*sizeof(model_t));
    for(int i = 0; i < model_count; i++){
        models[i] = GBcreateBase();
        GBsetChunkMethods(models[i],HREgreyboxNewmap,HREglobal(),
                          HREgreyboxI2C,
                          HREgreyboxC2I,
                          HREgreyboxCAtI,
                          HREgreyboxCount);
        GBsetModelNr(models[i], i);
        Warning(info, "Starting loader");
        loader(models[i], files[i]);
    }
    map = malloc(sizeof(mapping_t));
    map->map = malloc(model_count * sizeof(int*));
    map->maxLength = malloc(model_count * sizeof(int));
    map->length = malloc(model_count * sizeof(int));
    for(int i = 0; i < model_count; i++){
        map->map[i] = malloc(10*sizeof(int));
        map->maxLength[i] = 10;
        map->length[i] = 0;
    }

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
        combineSLMatrices(models, p_dm_state_label);
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
    char** txtFiles = malloc(model_count * sizeof(char*));
    for(int i = 0; i < model_count; i++){
        txtFiles[i] = files[i + model_count];
    }
    if(iomapa){
        create_correct_io_groups(composition, txtFiles, model_count);
    } else {
        create_correct_groups(composition, txtFiles, model_count);
    }

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
        static matrix_t p_dm_class;
        dm_create(&p_dm_class, rows_class[0], tot_columns_class);
        int class_columns_counted = 0;
        for(int i = 0; i < model_count; i++){
            for(int j = 0; j < rows_class[i]; j++){
                for(int k = 0; k < columns_class[i]; k++){
                    if(correct_groups[k + class_columns_counted] && dm_is_set(GBgetMatrix(models[i], id[i]), j, k)){
                        dm_set(&p_dm_class, j, k + class_columns_counted);
                    }
                }
            }
            class_columns_counted += columns_class[i];
        }
        //voor 2 modellen
        for(int i = 0; i < columns_class[0]; i++){
            for(int j = 0; j < columns_class[1]; j++){
                if (correct_groups[class_columns_counted + i * columns_class[1] + j]){
                    if ((dm_is_set(GBgetMatrix(models[0], id[0]), INPUT, i) && dm_is_set(GBgetMatrix(models[1], id[1]), OUTPUT, j)) || (dm_is_set(GBgetMatrix(models[0], id[0]), OUTPUT, i) && dm_is_set(GBgetMatrix(models[1], id[1]), INPUT, j))){
                        dm_set(&p_dm_class, OUTPUT, class_columns_counted + i * columns_class[1] + j);
                    } else {
                        for(int k = 0; k < rows_class[0]; k++){
                            if(dm_is_set(GBgetMatrix(models[0], id[0]), k, i) && dm_is_set(GBgetMatrix(models[1], id[1]), k, j)){
                                dm_set(&p_dm_class, k, class_columns_counted + i * columns_class[1] + j);
                            }
                        }
                    }
                }
            }
        }

        GBsetMatrix(composition,LTSMIN_EDGE_TYPE_ACTION_CLASS,&p_dm_class,PINS_STRICT,PINS_INDEX_OTHER,PINS_INDEX_GROUP);
        FILE* class = fopen("class.txt", "w+");
        dm_print(class, &p_dm_class);
        fclose(class);
    }

    //Inhibit matrix
    int inhibit_id = GBgetMatrixID(models[0], "inhibit");
    if(inhibit_id >= 0){
        static matrix_t p_dm_inhibit;
        int inhibit_rows = dm_nrows(GBgetMatrix(models[0], inhibit_id));
        int inhibit_cols = dm_ncols(GBgetMatrix(models[0], inhibit_id));
        dm_create(&p_dm_inhibit, inhibit_rows, inhibit_cols);
        for(int i = 0; i < inhibit_rows; i ++){
            for(int j = 0; j < inhibit_cols; j++){
                if(dm_is_set(GBgetMatrix(models[0], inhibit_id), i, j)){
                    dm_set(&p_dm_inhibit, i, j);
                }
            }
        }
        GBsetMatrix(composition,"inhibit",&p_dm_inhibit,PINS_STRICT,PINS_INDEX_OTHER,PINS_INDEX_OTHER);
    }

    //LTS Type
    lts_type_t ltstype = lts_type_create();
    bool_type=lts_type_put_type(ltstype,"Bool",LTStypeChunk,NULL);

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
        char model_nr_str[2];
        sprintf(model_nr_str, "%d", i);
        for (int j = 0; j < lts_type_get_state_length (GBgetLTStype(models[i])); j++){
            if(strcmp(lts_type_get_state_type(GBgetLTStype(models[i]), j), "Bool") != 0){
                char tmp[MAX_LABEL_LENGTH];
                strcpy(tmp, lts_type_get_state_name(GBgetLTStype(models[i]), j));
                strcat(strcat(tmp, "_"),model_nr_str);
                lts_type_set_state_name(ltstype, j + state_length_counted, tmp);
                strcpy(tmp, lts_type_get_state_type(GBgetLTStype(models[i]), j));
                strcat(strcat(tmp, "_"),model_nr_str);
                lts_type_set_state_type(ltstype, j + state_length_counted, tmp);
            } else {
                lts_type_set_state_name(ltstype, j + state_length_counted, lts_type_get_state_name(GBgetLTStype(models[i]), j));
                lts_type_set_state_type(ltstype, j + state_length_counted, lts_type_get_state_type(GBgetLTStype(models[i]), j));
            }
        }
        state_length_counted += lts_type_get_state_length (GBgetLTStype(models[i]));
        edge_labels_counted += lts_type_get_edge_label_count(GBgetLTStype(models[i]));
        state_labels_counted += lts_type_get_state_label_count(GBgetLTStype(models[i]));
    }
    lts_type_put_type(ltstype,"action",LTStypeChunk,NULL);
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

    lts_type_set_state_label_count(ltstype,3);
    lts_type_set_state_label_name(ltstype,0,"goal");
    lts_type_set_state_label_type(ltstype,0,"Bool");
    lts_type_set_state_label_name(ltstype,1,"state_reward_numerator");
    lts_type_set_state_label_type(ltstype,1,"nat");
    lts_type_set_state_label_name(ltstype,2,"state_reward_denominator");
    lts_type_set_state_label_type(ltstype,2,"pos");

    GBsetLTStype(composition, ltstype);
    GBchunkPutAt(composition,bool_type,chunk_str("F"),0);
    GBchunkPutAt(composition,bool_type,chunk_str("T"),1);

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


    GBsetNextStateLong(composition, getTransitionsLong);
    GBsetStateLabelLong(composition, getStateLabelLong);
    GBsetTransitionInGroup(composition, transitionInGroup);

    model_comp = &composition;
}

