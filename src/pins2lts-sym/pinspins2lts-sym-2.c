#include <hre/config.h>

#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>

#include <dm/dm.h>
#include <hre/user.h>
#include <lts-io/user.h>
#include <pins-lib/pg-types.h>
#include <pins-lib/pins.h>
#include <pins-lib/pins-impl.h>
#include <pins-lib/property-semantics.h>
#include <ltsmin-lib/ltsmin-standard.h>
#include <ltsmin-lib/ltsmin-syntax.h>
#include <ltsmin-lib/ltsmin-tl.h>
#include <spg-lib/spg-solve.h>
#include <vset-lib/vector_set.h>
#include <util-lib/dynamic-array.h>
#include <hre/stringindex.h>

static char* ctl_formula = NULL;
static char* mu_formula  = NULL;

static char* trc_output = NULL;
static int   dlk_detect = 0;
static char* act_detect = NULL;
static char* inv_detect = NULL;
static int   no_exit = 0;
static int   act_index;
static int   act_label;
static int   sat_granularity = 10;
static int   save_sat_levels = 0;

#ifdef HAVE_LIBSPG
static int   pgsolve_flag = 0;
static char* pg_output = NULL;
#endif
#if defined(LTSMIN_PBES)
static int   pgreduce_flag = 0;
#endif
static model_t model1;
static model_t model2;

/*
  The inhibit and class matrices are used for maximal progress.
 */
static matrix_t *inhibit_matrix=NULL;
static matrix_t *class_matrix=NULL;

static enum { BFS_P , BFS , CHAIN_P, CHAIN } strategy = BFS_P;

static char* order = "bfs-prev";
static si_map_entry ORDER[] = {
    {"bfs-prev", BFS_P},
    {"bfs", BFS},
    {"chain-prev", CHAIN_P},
    {"chain", CHAIN},
    {NULL, 0}
};

static enum { NO_SAT, SAT_LIKE, SAT_LOOP, SAT_FIX, SAT } sat_strategy = NO_SAT;

static char* saturation = "none";
static si_map_entry SATURATION[] = {
    {"none", NO_SAT},
    {"sat-like", SAT_LIKE},
    {"sat-loop", SAT_LOOP},
    {"sat-fix", SAT_FIX},
    {"sat", SAT},
    {NULL, 0}
};

static enum { UNGUIDED, DIRECTED } guide_strategy = UNGUIDED;

static char *guidance = "unguided";
static si_map_entry GUIDED[] = {
    {"unguided", UNGUIDED},
    {"directed", DIRECTED},
    {NULL, 0}
};

static void
reach_popt(poptContext con, enum poptCallbackReason reason,
               const struct poptOption * opt, const char * arg, void * data)
{
    (void)con; (void)opt; (void)arg; (void)data;

    switch (reason) {
    case POPT_CALLBACK_REASON_PRE:
        Abort("unexpected call to reach_popt");
    case POPT_CALLBACK_REASON_POST: {
        int res;

        res = linear_search(ORDER, order);
        if (res < 0) {
            Warning(error, "unknown exploration order %s", order);
            HREexitUsage(LTSMIN_EXIT_FAILURE);
        } else {
            Warning(info, "Exploration order is %s", order);
        }
        strategy = res;

        res = linear_search(SATURATION, saturation);
        if (res < 0) {
            Warning(error, "unknown saturation strategy %s", saturation);
            HREexitUsage(LTSMIN_EXIT_FAILURE);
        } else {
            Warning(info, "Saturation strategy is %s", saturation);
        }
        sat_strategy = res;

        res = linear_search(GUIDED, guidance);
        if (res < 0) {
            Warning(error, "unknown guided search strategy %s", guidance);
            HREexitUsage(LTSMIN_EXIT_FAILURE);
        } else {
            Warning(info, "Guided search strategy is %s", guidance);
        }
        guide_strategy = res;

        if (trc_output != NULL && !dlk_detect && act_detect == NULL)
            Warning(info, "Ignoring trace output");

        return;
    }
    case POPT_CALLBACK_REASON_OPTION:
        Abort("unexpected call to reach_popt");
    }
}

static  struct poptOption options[] = {
    { NULL, 0 , POPT_ARG_CALLBACK|POPT_CBFLAG_POST|POPT_CBFLAG_SKIPOPTION , (void*)reach_popt , 0 , NULL , NULL },
    { "order" , 0 , POPT_ARG_STRING|POPT_ARGFLAG_SHOW_DEFAULT , &order , 0 , "set the exploration strategy to a specific order" , "<bfs-prev|bfs|chain-prev|chain>" },
    { "saturation" , 0, POPT_ARG_STRING|POPT_ARGFLAG_SHOW_DEFAULT , &saturation , 0 , "select the saturation strategy" , "<none|sat-like|sat-loop|sat-fix|sat>" },
    { "sat-granularity" , 0 , POPT_ARG_INT|POPT_ARGFLAG_SHOW_DEFAULT, &sat_granularity , 0 , "set saturation granularity","<number>" },
    { "save-sat-levels", 0, POPT_ARG_VAL, &save_sat_levels, 1, "save previous states seen at saturation levels", NULL },
    { "guidance", 0 , POPT_ARG_STRING|POPT_ARGFLAG_SHOW_DEFAULT , &guidance, 0 , "select the guided search strategy" , "<unguided|directed>" },
    { "deadlock" , 'd' , POPT_ARG_VAL , &dlk_detect , 1 , "detect deadlocks" , NULL },
    { "action" , 0 , POPT_ARG_STRING , &act_detect , 0 , "detect action" , "<action>" },
    { "invariant", 'i', POPT_ARG_STRING, &inv_detect, 1, "detect deadlocks", NULL },
    { "no-exit", 'n', POPT_ARG_VAL, &no_exit, 1, "no exit on error, just count (for error counters use -v)", NULL },
    { "trace" , 0 , POPT_ARG_STRING , &trc_output , 0 , "file to write trace to" , "<lts-file>.gcf" },
    { "mu" , 0 , POPT_ARG_STRING , &mu_formula , 0 , "file with a mu formula" , "<mu-file>.mu" },
    { "ctl-star" , 0 , POPT_ARG_STRING , &ctl_formula , 0 , "file with a ctl* formula" , "<ctl-file>.ctl" },
#ifdef HAVE_LIBSPG
    { "pg-solve" , 0 , POPT_ARG_NONE , &pgsolve_flag, 0, "Solve the generated parity game (only for symbolic tool).","" },
    { NULL, 0 , POPT_ARG_INCLUDE_TABLE, spg_solve_options , 0, "Symbolic parity game solver options", NULL},
#if defined(LTSMIN_PBES)
    { "pg-reduce" , 0 , POPT_ARG_NONE , &pgreduce_flag, 0, "Reduce the generated parity game on-the-fly (only for symbolic tool).","" },
#endif
    { "pg-write" , 0 , POPT_ARG_STRING , &pg_output, 0, "file to write symbolic parity game to","<pg-file>.spg" },
#endif
    SPEC_POPT_OPTIONS,
    { NULL, 0 , POPT_ARG_INCLUDE_TABLE, greybox_options , 0 , "PINS options",NULL},
    { NULL, 0 , POPT_ARG_INCLUDE_TABLE, vset_options , 0 , "Vector set options",NULL},
    POPT_TABLEEND
};

typedef struct {
    int len;
    int *proj;
} proj_info;

static lts_type_t ltstype;
static int N;
static int eLbls;
static int sLbls;
static int nGrps;
static int max_sat_levels;
//For second model
static lts_type_t ltstype2;
static int N2;
static int eLbls2;
static int sLbls2;
static int nGrps2;
static int max_sat_levels2;

static proj_info *projs;
static vdom_t domain;
static vset_t *levels = NULL;
static int max_levels = 0;
static int global_level;
static long max_lev_count = 0;
static long max_vis_count = 0;
static long max_grp_count = 0;
static long max_trans_count = 0;
static model_t model;
static vrel_t *group_next;
static vset_t *group_explored;
static vset_t *group_tmp;

typedef void (*reach_proc_t)(vset_t visited, vset_t visited_old,
                             bitvector_t *reach_groups,
                             long *eg_count, long *next_count);

typedef void (*sat_proc_t)(reach_proc_t reach_proc, vset_t visited,
                           bitvector_t *reach_groups,
                           long *eg_count, long *next_count);

typedef void (*guided_proc_t)(sat_proc_t sat_proc, reach_proc_t reach_proc,
                              vset_t visited, char *etf_output);

static inline void
grow_levels(int new_levels)
{
    if (global_level == max_levels) {
        max_levels += new_levels;
        levels = RTrealloc(levels, max_levels * sizeof(vset_t));

        for(int i = global_level; i < max_levels; i++)
            levels[i] = vset_create(domain, -1, NULL);
    }
}

static inline void
save_level(vset_t visited)
{
    grow_levels(1024);
    vset_copy(levels[global_level], visited);
    global_level++;
}

static void
write_trace_state(lts_file_t trace_handle, int src_no, int *state)
{
  int labels[sLbls];

  Warning(debug, "dumping state %d", src_no);

  if (sLbls != 0)
      GBgetStateLabelsAll(model, state, labels);

  lts_write_state(trace_handle, 0, state, labels);
}

struct write_trace_step_s {
    lts_file_t    trace_handle;
    int           src_no;
    int           dst_no;
    int          *dst;
    int           found;
};

static void
write_trace_next(void *arg, transition_info_t *ti, int *dst)
{
    struct write_trace_step_s *ctx = (struct write_trace_step_s*)arg;

    if (ctx->found)
        return;

    for(int i = 0; i < N; i++) {
        if (ctx->dst[i] != dst[i])
            return;
    }

    ctx->found = 1;
    lts_write_edge(ctx->trace_handle, 0, &ctx->src_no, 0, dst, ti->labels);
}

static void
write_trace_step(lts_file_t trace_handle, int src_no, int *src,
                 int dst_no, int *dst)
{
    struct write_trace_step_s ctx;

    Warning(debug, "finding edge for state %d", src_no);
    ctx.trace_handle = trace_handle;
    ctx.src_no = src_no;
    ctx.dst_no = dst_no;
    ctx.dst = dst;
    ctx.found = 0;

    GBgetTransitionsAll(model, src, write_trace_next, &ctx);

    if (!ctx.found)
        Abort("no matching transition found");
}

static void
write_trace(lts_file_t trace_handle, int **states, int total_states)
{
    // output starting from initial state, which is in states[total_states-1]

    for(int i = total_states - 1; i > 0; i--) {
        int current_step = total_states - i - 1;

        write_trace_state(trace_handle, current_step, states[i]);
        write_trace_step(trace_handle, current_step, states[i],
                         current_step + 1, states[i - 1]);
    }

    write_trace_state(trace_handle, total_states - 1, states[0]);
}

static void
find_trace_to(int trace_end[][N], int end_count, int level, vset_t *levels,
              lts_file_t trace_handle)
{
    int    prev_level   = level - 2;
    vset_t src_set      = vset_create(domain, -1, NULL);
    vset_t dst_set      = vset_create(domain, -1, NULL);
    vset_t temp         = vset_create(domain, -1, NULL);

    int   max_states    = 1024 + end_count;
    int   current_state = end_count;
    int **states        = RTmalloc(sizeof(int*[max_states]));

    for (int i = 0; i < end_count; i++)
        states[i] = trace_end[i];

    for(int i = end_count; i < max_states; i++)
        states[i] = RTmalloc(sizeof(int[N]));

    int     max_int_level  = 32;
    vset_t *int_levels     = RTmalloc(sizeof(vset_t[max_int_level]));

    for(int i = 0; i < max_int_level; i++)
        int_levels[i] = vset_create(domain, -1, NULL);

    while (prev_level >= 0) {
        int int_level = 0;

        if (vset_member(levels[prev_level], states[current_state - 1])) {
            Warning(debug, "Skipping level %d in trace generation", prev_level);
            prev_level--;
            continue;
        }

        vset_add(int_levels[0], states[current_state - 1]);

        // search backwards from states[current_state - 1] to prev_level
        do {
            int_level++;

            if (int_level == max_int_level) {
                max_int_level += 32;
                int_levels = RTrealloc(int_levels,
                                           sizeof(vset_t[max_int_level]));

                for(int i = int_level; i < max_int_level; i++)
                    int_levels[i] = vset_create(domain, -1, NULL);
            }

            for (int i=0; i < nGrps; i++) {
                vset_prev(temp, int_levels[int_level - 1], group_next[i]);
                vset_union(int_levels[int_level], temp);
            }

            vset_copy(temp, levels[prev_level]);
            vset_minus(temp, int_levels[int_level]);
        } while (vset_equal(levels[prev_level], temp));

        if (current_state + int_level >= max_states) {
            int old_max_states = max_states;

            max_states = current_state + int_level + 1024;
            states = RTrealloc(states,sizeof(int*[max_states]));

            for(int i = old_max_states; i < max_states; i++)
                states[i] = RTmalloc(sizeof(int[N]));
        }

        // here: temp = levels[prev_level] - int_levels[int_level]
        vset_copy(src_set, levels[prev_level]);
        vset_minus(src_set, temp);
        vset_example(src_set, states[current_state + int_level - 1]);
        vset_clear(src_set);

        // find the states that give us a trace to states[current_state - 1]
        for(int i = int_level - 1; i > 0; i--) {
            vset_add(src_set, states[current_state + i]);

            for(int j = 0; j < nGrps; j++) {
                vset_next(temp, src_set, group_next[j]);
                vset_union(dst_set, temp);
            }

            vset_copy(temp, dst_set);
            vset_minus(temp, int_levels[i]);
            vset_minus(dst_set, temp);
            vset_example(dst_set, states[current_state + i - 1]);
            vset_clear(src_set);
            vset_clear(dst_set);
        }

        current_state += int_level;
        prev_level--;

        for(int i = 0; i <= int_level; i++)
            vset_clear(int_levels[i]);

        vset_clear(temp);
    }

    write_trace(trace_handle, states, current_state);
}

static void
find_trace(int trace_end[][N], int end_count, int level, vset_t *levels)
{
    // Find initial state and open output file
    int             init_state[N];
    lts_file_t      trace_output;
    lts_type_t      ltstype = GBgetLTStype(model);

    GBgetInitialState(model1, init_state);

    trace_output = lts_file_create(trc_output, ltstype, 1, lts_vset_template());
    lts_write_init(trace_output, 0, (uint32_t*)init_state);
    int T=lts_type_get_type_count(ltstype);
    for(int i=0;i<T;i++){
        lts_file_set_table(trace_output,i,GBgetChunkMap(model,i));
    }

    // Generate trace
    rt_timer_t  timer = RTcreateTimer();

    RTstartTimer(timer);
    find_trace_to(trace_end, end_count, level, levels, trace_output);
    RTstopTimer(timer);
    RTprintTimer(info, timer, "constructing trace took");

    // Close output file
    lts_file_close(trace_output);
}

struct find_action_info {
    int  group;
    int *dst;
};

static void
find_action_cb(void* context, int* src)
{
    struct find_action_info* ctx = (struct find_action_info*)context;
    int group=ctx->group;
    int trace_end[2][N];

    for (int i = 0; i < N; i++) {
        trace_end[0][i] = src[i];
        trace_end[1][i] = src[i];
    }

    // Set dst of the last step of the trace to its proper value
    for (int i = 0; i < projs[group].len; i++)
        trace_end[0][projs[group].proj[i]] = ctx->dst[i];

    // src and dst may both be new, e.g. in case of chaining
    if (vset_member(levels[global_level - 1], src)) {
        Warning(debug, "source found at level %d", global_level - 1);
        find_trace(trace_end, 2, global_level, levels);
    } else {
        Warning(debug, "source not found at level %d", global_level - 1);
        find_trace(trace_end, 2, global_level + 1, levels);
    }

    Warning(info, "exiting now");
    HREabort(LTSMIN_EXIT_COUNTER_EXAMPLE);
}

struct group_add_info {
    int    group;
    int   *src;
    int   *explored;
    vset_t set;
    vrel_t rel;
};

static void
group_add(void *context, transition_info_t *ti, int *dst)
{
    struct group_add_info *ctx = (struct group_add_info*)context;

    vrel_add(ctx->rel, ctx->src, dst);

    if (act_detect != NULL && ti->labels[act_label] == act_index) {
        Warning(info, "found action: %s", act_detect);

        if (trc_output == NULL){
            Warning(info, "exiting now");
            HREabort(LTSMIN_EXIT_COUNTER_EXAMPLE);
        }

        struct find_action_info action_ctx;
        int group = ctx->group;

        action_ctx.group = group;
        action_ctx.dst = dst;
        vset_enum_match(ctx->set,projs[group].len, projs[group].proj,
                            ctx->src, find_action_cb, &action_ctx);
    }
}

static void
explore_cb(void *context, int *src)
{
    struct group_add_info *ctx = (struct group_add_info*)context;

    ctx->src = src;
    GBgetTransitionsShort(model1, ctx->group, src, group_add, context);
    (*ctx->explored)++;

    if ((*ctx->explored) % 10000 == 0) {
        Warning(infoLong, "explored %d short vectors for group %d",
                    *ctx->explored, ctx->group);
    }
}

static inline void
expand_group_next(int group, vset_t set)
{
    struct group_add_info ctx;
    int explored = 0;

    ctx.group = group;
    ctx.set = set;
    ctx.rel = group_next[group];
    ctx.explored = &explored;
    vset_project(group_tmp[group], set);
    vset_zip(group_explored[group], group_tmp[group]);
    vset_enum(group_tmp[group], explore_cb, &ctx);
    vset_clear(group_tmp[group]);
}

static void
valid_end_cb(void *context, int *src)
{
    int *state = (int *) context;
    if (!state[N] && !GBstateIsValidEnd(model, src)) {
        memcpy (state, src, sizeof(int[N]));
        state[N] = 1;
    }
}

static void
deadlock_check(vset_t deadlocks, bitvector_t *reach_groups)
{
    if (vset_is_empty(deadlocks))
        return;

    vset_t next_temp = vset_create(domain, -1, NULL);
    vset_t prev_temp = vset_create(domain, -1, NULL);

    Warning(debug, "Potential deadlocks found");

    for (int i = 0; i < nGrps; i++) {
        if (bitvector_is_set(reach_groups, i)) continue;
        expand_group_next(i, deadlocks);
        vset_next(next_temp, deadlocks, group_next[i]);
        vset_prev(prev_temp, next_temp, group_next[i]);
        vset_minus(deadlocks, prev_temp);
    }

    vset_destroy(next_temp);
    vset_destroy(prev_temp);

    if (vset_is_empty(deadlocks))
        return;

    int dlk_state[1][N + 1];
    if (GBgetValidEndStateLabelIndex(model) >= 0) {
        dlk_state[0][N] = 0; // Did not find an invalid end state yet
        vset_enum (deadlocks, valid_end_cb, dlk_state[0]);
        if (!dlk_state[0][N])
            return;
    } else {
        vset_example(deadlocks, dlk_state[0]);
    }

    Warning(info, "deadlock found");

    if (trc_output) {
        find_trace(dlk_state, 1, global_level, levels);
    }

    Warning(info, "exiting now");
    HREabort(LTSMIN_EXIT_COUNTER_EXAMPLE);
}

static inline void
get_vset_size(vset_t set, long *node_count, double *elem_approximation,
                  char *elem_str, ssize_t str_len)
{
    bn_int_t elem_count;
    int      len;

    vset_count(set, node_count, &elem_count);
    len = bn_int2string(elem_str, str_len, &elem_count);

    if (len >= str_len)
        Abort("Error converting number to string");

    *elem_approximation = bn_int2double(&elem_count);

    bn_clear(&elem_count);
}

static inline void
get_vrel_size(vrel_t rel, long *node_count, double *elem_approximation,
                  char *elem_str, ssize_t str_len)
{
    bn_int_t elem_count;
    int      len;

    vrel_count(rel, node_count, &elem_count);
    len = bn_int2string(elem_str, str_len, &elem_count);

    if (len >= str_len)
        Abort("Error converting number to string");

    *elem_approximation = bn_int2double(&elem_count);

    bn_clear(&elem_count);
}

static void
stats_and_progress_report(vset_t current, vset_t visited, int level)
{
    long   n_count;
    char   elem_str[1024];
    double e_count;
    
    if (sat_strategy == NO_SAT || log_active(infoLong)) Print(infoShort, "level %d is finished",level);
    if (log_active(infoLong)) {
      if (current != NULL) {
        get_vset_size(current, &n_count, &e_count, elem_str, sizeof(elem_str));
        Print(infoLong, "level %d has %s (~%1.2e) states ( %ld nodes )",
	      level, elem_str, e_count, n_count);
        if (n_count > max_lev_count)
	  max_lev_count = n_count;
      }
      get_vset_size(visited, &n_count, &e_count, elem_str, sizeof(elem_str));
      Print(infoLong, "visited %d has %s (~%1.2e) states ( %ld nodes )",
	    level, elem_str, e_count, n_count);
      
      if (n_count > max_vis_count)
        max_vis_count = n_count;
      
      if (log_active(debug)) {
        Debug("transition caches ( grp nds elts ):");
	
        for (int i = 0; i < nGrps; i++) {
	  get_vrel_size(group_next[i], &n_count, &e_count, elem_str,
			sizeof(elem_str));
	  Debug("( %d %ld %s ) ", i, n_count, elem_str);
	  
	  if (n_count > max_trans_count)
	    max_trans_count = n_count;
        }
	
        Debug("\ngroup explored    ( grp nds elts ): ");
	
        for (int i = 0; i < nGrps; i++) {
	  get_vset_size(group_explored[i], &n_count, &e_count, elem_str,
			sizeof(elem_str));
	  Debug("( %d %ld %s ) ", i, n_count, elem_str);
	  
	  if (n_count > max_grp_count)
	    max_grp_count = n_count;
        }
      }
    }
}

static void
final_stat_reporting(vset_t visited, rt_timer_t timer)
{
    long   n_count;
    char   elem_str[1024];
    double e_count;

    RTprintTimer(info,timer, "reachability took");

    if (dlk_detect)
        Warning(info, "No deadlocks found");

    if (act_detect != NULL)
        Warning(info, "Action \"%s\" not found", act_detect);

    get_vset_size(visited, &n_count, &e_count, elem_str, sizeof(elem_str));
    Print(infoShort, "state space has %s (~%1.2e) states, %ld BDD nodes", elem_str, e_count,n_count);

    if (log_active(infoLong)) {
      if (max_lev_count == 0) {
        Print(infoLong, "( %ld final BDD nodes; %ld peak nodes )",
	      n_count, max_vis_count);
      } else {
        Print(infoLong, "( %ld final BDD nodes; %ld peak nodes; "
	      "%ld peak nodes per level )",
	      n_count, max_vis_count, max_lev_count);
      }
      
      if (log_active(debug)) {
	Debug("( peak transition cache: %ld nodes; peak group explored: "
	      "%ld nodes )\n", max_trans_count, max_grp_count);
      }
    }
}

static void
reach_bfs_prev(vset_t visited, vset_t visited_old, bitvector_t *reach_groups,
                   long *eg_count, long *next_count)
{
    int N=0;
    if (inhibit_matrix!=NULL){
        N=dm_nrows(inhibit_matrix);
    }
    int level = 0;
    vset_t current_level = vset_create(domain, -1, NULL);///L
    vset_t current_class = vset_create(domain, -1, NULL);
    vset_t next_level    = vset_create(domain, -1, NULL);
    vset_t temp          = vset_create(domain, -1, NULL);
    vset_t deadlocks     = dlk_detect?vset_create(domain, -1, NULL):NULL;
    vset_t dlk_temp      = (dlk_detect||N>0)?vset_create(domain, -1, NULL):NULL;
    vset_t enabled[N];
    //for 1 <= i <= K
    for(int i=0;i<N;i++){
        enabled[i]=vset_create(domain, -1, NULL);
    }

    vset_copy(current_level, visited);// L <- R
    if (save_sat_levels) vset_minus(current_level, visited_old);

    while (!vset_is_empty(current_level)) {// While L != {empty}
        //Learn-Trans
        if (trc_output != NULL) save_level(visited);
        stats_and_progress_report(current_level, visited, level);
        level++;
        for (int i = 0; i < nGrps; i++){
            if (!bitvector_is_set(reach_groups, i)) continue;
            expand_group_next(i, current_level);
            (*eg_count)++;
        }
        //End Learn-Trans
        for(int i=0;i<N;i++){
            vset_clear(enabled[i]);// N <- {empty}
        }
        if (dlk_detect) vset_copy(deadlocks, current_level);
        if (N>0){
            for(int c=0;c<N;c++){
                vset_copy(current_class,current_level);
                for(int i=0;i<c;i++){
                    if (dm_is_set(inhibit_matrix,i,c)){
                        vset_minus(current_class, enabled[i]);
                    }
                }
                for (int i = 0; i < nGrps; i++) {
                    if (!bitvector_is_set(reach_groups,i)) continue;
                    if (!dm_is_set(class_matrix,c,i)) continue;
                    (*next_count)++;
                    vset_next(temp, current_class, group_next[i]);
                    vset_prev(dlk_temp, temp, group_next[i]);
                    if (dlk_detect) {
                        vset_minus(deadlocks, dlk_temp);
                    }
                    vset_union(enabled[c],dlk_temp);
                    vset_clear(dlk_temp);
                    vset_minus(temp, visited);
                    vset_union(next_level, temp);
                    vset_clear(temp);
                }
                vset_clear(current_class);
            }
        } else {
            for (int i = 0; i < nGrps; i++) {
                if (!bitvector_is_set(reach_groups,i)) continue;
                (*next_count)++;
                vset_next(temp, current_level, group_next[i]);
                if (dlk_detect) {
                    vset_prev(dlk_temp, temp, group_next[i]);
                    vset_minus(deadlocks, dlk_temp);
                    vset_clear(dlk_temp);
                }
                vset_minus(temp, visited);
                vset_union(next_level, temp);
                vset_clear(temp);
            }
        }
        if (dlk_detect) deadlock_check(deadlocks, reach_groups);

#if defined(LTSMIN_PBES)
        if (pgreduce_flag) reduce_parity_game(next_level, visited, true_states, false_states);
#endif

        vset_union(visited, next_level);
        vset_copy(current_level, next_level);
        vset_clear(next_level);
        vset_reorder(domain);
    }

    vset_destroy(current_level);
    vset_destroy(next_level);
    vset_destroy(temp);
    if (dlk_detect) {
        vset_destroy(deadlocks);
        vset_destroy(dlk_temp);
    }
}

static void
reach_no_sat(reach_proc_t reach_proc, vset_t visited, bitvector_t *reach_groups,
                 long *eg_count, long *next_count)
{
    vset_t old_visited = save_sat_levels?vset_create(domain, -1, NULL):NULL;

    reach_proc(visited, old_visited, reach_groups, eg_count, next_count);

    if (save_sat_levels) vset_destroy(old_visited);
}



struct expand_info {
    int group;
    vset_t group_explored;
    long *eg_count;
};


typedef struct {
    model_t  model;
    FILE    *tbl_file;
    int      tbl_count;
    int      group;
    int     *src;
} output_context;

static void
etf_edge(void *context, transition_info_t *ti, int *dst)
{
    output_context* ctx = (output_context*)context;

    ctx->tbl_count++;

    for(int i = 0, k = 0 ; i < N; i++) {
        if (dm_is_set(GBgetDMInfo(ctx->model), ctx->group, i)) {
            fprintf(ctx->tbl_file, " %d/%d", ctx->src[k], dst[k]);
            k++;
        } else {
            fprintf(ctx->tbl_file," *");
        }
    }

    for(int i = 0; i < eLbls; i++)
        fprintf(ctx->tbl_file, " %d", ti->labels[i]);

    fprintf(ctx->tbl_file,"\n");
}

static void enum_edges(void *context, int *src)
{
    output_context* ctx = (output_context*)context;

    ctx->src = src;
    GBgetTransitionsShort(model1, ctx->group, ctx->src, etf_edge, context);
}

typedef struct {
    FILE *tbl_file;
    int   mapno;
    int   len;
    int  *used;
} map_context;

static void
enum_map(void *context, int *src){
    map_context *ctx = (map_context*)context;
    int val = GBgetStateLabelShort(model, ctx->mapno, src);

    for (int i = 0, k = 0; i < N; i++) {
        if (k < ctx->len && ctx->used[k] == i){
            fprintf(ctx->tbl_file, "%d ", src[k]);
            k++;
        } else {
            fprintf(ctx->tbl_file, "* ");
        }
    }

    fprintf(ctx->tbl_file, "%d\n", val);
}

static void
output_init(FILE *tbl_file)
{
    int state[N];

    GBgetInitialState(model1, state);
    fprintf(tbl_file, "begin state\n");

    for (int i = 0; i < N; i++) {
        fprint_ltsmin_ident(tbl_file, lts_type_get_state_name(ltstype, i));
        fprintf(tbl_file, ":");
        fprint_ltsmin_ident(tbl_file, lts_type_get_state_type(ltstype, i));
        fprintf(tbl_file, (i == (N - 1))?"\n":" ");
    }

    fprintf(tbl_file,"end state\n");

    fprintf(tbl_file,"begin edge\n");
    for(int i = 0; i < eLbls; i++) {
        fprint_ltsmin_ident(tbl_file, lts_type_get_edge_label_name(ltstype, i));
        fprintf(tbl_file, ":");
        fprint_ltsmin_ident(tbl_file, lts_type_get_edge_label_type(ltstype, i));
        fprintf(tbl_file, (i == (eLbls - 1))?"\n":" ");
    }

    fprintf(tbl_file, "end edge\n");

    fprintf(tbl_file, "begin init\n");

    for(int i = 0; i < N; i++)
        fprintf(tbl_file, "%d%s", state[i], (i == (N - 1))?"\n":" ");

    fprintf(tbl_file,"end init\n");
}

static void
output_trans(FILE *tbl_file)
{
    int tbl_count = 0;
    output_context ctx;

    ctx.model = model;
    ctx.tbl_file = tbl_file;

    for(int g = 0; g < nGrps; g++) {
        ctx.group = g;
        ctx.tbl_count = 0;
        fprintf(tbl_file, "begin trans\n");
        vset_enum(group_explored[g], enum_edges, &ctx);
        fprintf(tbl_file, "end trans\n");
        tbl_count += ctx.tbl_count;
    }

    Warning(info, "Symbolic tables have %d reachable transitions", tbl_count);
}

static void
output_lbls(FILE *tbl_file, vset_t visited)
{
    matrix_t *sl_info = GBgetStateLabelInfo(model);

    sLbls = dm_nrows(sl_info);

    if (dm_nrows(sl_info) != lts_type_get_state_label_count(ltstype))
        Warning(error, "State label count mismatch!");

    for (int i = 0; i < sLbls; i++){
        int len = dm_ones_in_row(sl_info, i);
        int used[len];

        // get projection
        for (int pi = 0, pk = 0; pi < dm_ncols (sl_info); pi++) {
            if (dm_is_set (sl_info, i, pi))
                used[pk++] = pi;
        }

        vset_t patterns = vset_create(domain, len, used);
        map_context ctx;

        vset_project(patterns, visited);
        ctx.tbl_file = tbl_file;
        ctx.mapno = i;
        ctx.len = len;
        ctx.used = used;
        fprintf(tbl_file, "begin map ");
        fprint_ltsmin_ident(tbl_file, lts_type_get_state_label_name(ltstype,i));
        fprintf(tbl_file, ":");
        fprint_ltsmin_ident(tbl_file, lts_type_get_state_label_type(ltstype,i));
        fprintf(tbl_file,"\n");
        vset_enum(patterns, enum_map, &ctx);
        fprintf(tbl_file, "end map\n");
        vset_destroy(patterns);
    }
}

static void
output_types(FILE *tbl_file)
{
    int type_count = lts_type_get_type_count(ltstype);

    for (int i = 0; i < type_count; i++) {
        Warning(info, "dumping type %s", lts_type_get_type(ltstype, i));
        fprintf(tbl_file, "begin sort ");
        fprint_ltsmin_ident(tbl_file, lts_type_get_type(ltstype, i));
        fprintf(tbl_file, "\n");

        int values = GBchunkCount(model,i);

        for (int j = 0; j < values; j++) {
            chunk c    = GBchunkGet(model, i, j);
            size_t len = c.len * 2 + 6;
            char str[len];

            chunk2string(c, len, str);
            fprintf(tbl_file, "%s\n", str);
        }

        fprintf(tbl_file,"end sort\n");
    }
}

static void
do_output(char *etf_output, vset_t visited)
{
    FILE      *tbl_file;
    rt_timer_t  timer    = RTcreateTimer();

    RTstartTimer(timer);
    Warning(info, "writing output");
    tbl_file = fopen(etf_output, "w");

    if (tbl_file == NULL)
        AbortCall("could not open %s", etf_output);

    output_init(tbl_file);
    output_trans(tbl_file);
    output_lbls(tbl_file, visited);
    output_types(tbl_file);

    fclose(tbl_file);
    RTstopTimer(timer);
    RTprintTimer(info, timer, "writing output took");
}

static void
unguided(sat_proc_t sat_proc, reach_proc_t reach_proc, vset_t visited,
             char *etf_output)
{
    (void)etf_output;

    bitvector_t reach_groups;
    long eg_count = 0;
    long next_count = 0;

    bitvector_create(&reach_groups, nGrps);
    bitvector_invert(&reach_groups);
    sat_proc(reach_proc, visited, &reach_groups, &eg_count, &next_count);
    bitvector_free(&reach_groups);
    Warning(info, "Exploration took %ld group checks and %ld next state calls",
                eg_count, next_count);
}


static void
init_model1(char *file)
{
    Warning(info, "opening %s", file);
    model1 = GBcreateBase();
    GBsetChunkMethods(model1,HREgreyboxNewmap,HREglobal(),
                      HREgreyboxI2C,
                      HREgreyboxC2I,
                      HREgreyboxCAtI,
                      HREgreyboxCount);

    GBloadFile(model1, file, &model1);

    if (log_active(infoLong)) {
        fprintf(stderr, "Dependency Matrix:\n");
        GBprintDependencyMatrixCombined(stderr, model1);
    }

    ltstype = GBgetLTStype(model1);
    N = lts_type_get_state_length(ltstype);
    eLbls = lts_type_get_edge_label_count(ltstype);
    sLbls = lts_type_get_state_label_count(ltstype);
    nGrps = dm_nrows(GBgetDMInfo(model1));
    max_sat_levels = (N / sat_granularity) + 1;
    Warning(info, "state vector length is %d; there are %d groups", N, nGrps);

    int id=GBgetMatrixID(model1,"inhibit");
    if (id>=0){
        inhibit_matrix=GBgetMatrix(model1,id);
        Warning(infoLong,"inhibit matrix is:");
        if (log_active(infoLong)) dm_print(stderr,inhibit_matrix);
    }
    id = GBgetMatrixID(model1,LTSMIN_EDGE_TYPE_ACTION_CLASS);
    if (id>=0){
        class_matrix=GBgetMatrix(model1,id);
        Warning(infoLong,"inhibit class matrix is:");
        if (log_active(infoLong)) dm_print(stderr,class_matrix);
    }
}

static void
init_model2(char *file)
{
    Warning(info, "opening %s", file);
    model2 = GBcreateBase();
    GBsetChunkMethods(model2,HREgreyboxNewmap,HREglobal(),
                      HREgreyboxI2C,
                      HREgreyboxC2I,
                      HREgreyboxCAtI,
                      HREgreyboxCount);
    GBloadFile(model2, file, &model2);
    if (log_active(infoLong)) {
        fprintf(stderr, "Dependency Matrix:\n");
        GBprintDependencyMatrixCombined(stderr, model2);
    }
    ltstype2 = GBgetLTStype(model2);
    N2 = lts_type_get_state_length(ltstype2);
    eLbls2 = lts_type_get_edge_label_count(ltstype2);
    sLbls2 = lts_type_get_state_label_count(ltstype2);
    nGrps2 = dm_nrows(GBgetDMInfo(model2));
    max_sat_levels2 = (N2 / sat_granularity) + 1;
    Warning(info, "state vector length is %d; there are %d groups", N2, nGrps2);

    int id=GBgetMatrixID(model2,"inhibit");
    if (id>=0){
        inhibit_matrix=GBgetMatrix(model2,id);
        Warning(infoLong,"inhibit matrix is:");
        if (log_active(infoLong)) dm_print(stderr,inhibit_matrix);
    }
    id = GBgetMatrixID(model2,LTSMIN_EDGE_TYPE_ACTION_CLASS);
    if (id>=0){
        class_matrix=GBgetMatrix(model2,id);
        Warning(infoLong,"inhibit class matrix is:");
        if (log_active(infoLong)) dm_print(stderr,class_matrix);
    }
}

static void
init_domain(vset_implementation_t impl, vset_t *visited)
{
    domain = vdom_create_domain(N, impl);
    *visited = vset_create(domain, -1, NULL);

    group_next     = (vrel_t*)RTmalloc(nGrps * sizeof(vrel_t));
    group_explored = (vset_t*)RTmalloc(nGrps * sizeof(vset_t));
    group_tmp      = (vset_t*)RTmalloc(nGrps * sizeof(vset_t));
    projs          = (proj_info*)RTmalloc(nGrps * sizeof(proj_info));

    for(int i = 0; i < nGrps; i++) {
        projs[i].len  = dm_ones_in_row(GBgetDMInfo(model1), i);
        projs[i].proj = (int*)RTmalloc(projs[i].len * sizeof(int));

        // temporary replacement for e_info->indices[i]
        for(int j = 0, k = 0; j < dm_ncols(GBgetDMInfo(model1)); j++) {
            if (dm_is_set(GBgetDMInfo(model1), i, j))
                projs[i].proj[k++] = j;
        }

        group_next[i]     = vrel_create(domain,projs[i].len,projs[i].proj);
        group_explored[i] = vset_create(domain,projs[i].len,projs[i].proj);
        group_tmp[i]      = vset_create(domain,projs[i].len,projs[i].proj);
    }
}

static void
init_action()
{
    // table number of first edge label
    act_label = lts_type_find_edge_label_prefix (ltstype, LTSMIN_EDGE_TYPE_ACTION_PREFIX);
    if (act_label == -1)
        Abort("No edge label '%s...' for action detection", LTSMIN_EDGE_TYPE_ACTION_PREFIX);
    int typeno = lts_type_get_edge_label_typeno(ltstype, act_label);
    chunk c = chunk_str(act_detect);
    act_index = GBchunkPut(model, typeno, c);
    Warning(info, "Detecting action \"%s\"", act_detect);
}



int
main (int argc, char *argv[])
{
//    output = atoi(argv[3]);
//    choice = 0;
    char *file_choice = argv[2];
    for(int i = 2; i < argc - 2; i++){
        argv[i] = argv[i+2];
    }
    argc -= 2;
    char *files[3];
    HREinitBegin(argv[0]);
    HREaddOptions(options,"Perform a symbolic reachability analysis of <model>\n"
                  "The optional output of this analysis is an ETF "
                      "representation of the input\n\nOptions");
    lts_lib_setup();
    HREinitStart(&argc,&argv,1,2,files,"<model> [<etf>]");
    files[2] = files[1];
    files[1] = file_choice;
    vset_implementation_t vset_impl = VSET_IMPL_AUTOSELECT;
    vset_t visited;

    init_model1(files[0]);
    init_model2(files[1]);
    init_domain(vset_impl, &visited);
    if (act_detect != NULL) init_action();
    if (inv_detect) Abort("Invariant violation detection is not implemented.");
    if (no_exit) Abort("Error counting (--no-exit) is not implemented.");
    if (PINS_POR != PINS_POR_NONE) Abort("Partial-order reduction and symbolic model checking are not compatible.");


    if (inhibit_matrix!=NULL){
        if (strategy != BFS_P) Abort("maximal progress works for bfs-prev only.");
        if (sat_strategy != NO_SAT) Abort("maximal progress is incompatibale with saturation");
    }

    sat_proc_t sat_proc = NULL;
    reach_proc_t reach_proc = NULL;
    guided_proc_t guided_proc = NULL;
    switch (strategy) {
    case BFS_P:
        reach_proc = reach_bfs_prev;
        break;
    }

    switch (sat_strategy) {
    case NO_SAT:
        sat_proc = reach_no_sat;
        break;
    }

    switch (guide_strategy) {
    case UNGUIDED:
        guided_proc = unguided;
        break;
    }
    reach_proc = reach_bfs_prev;
    int src[N];
    GBgetInitialState(model1, src);
    vset_add(visited, src);
    Warning(info, "got initial state");

    rt_timer_t timer = RTcreateTimer();

    RTstartTimer(timer);
    guided_proc(sat_proc, reach_proc, visited, files[1]);
    RTstopTimer(timer);
    final_stat_reporting(visited, timer);

    if (log_active(infoLong)) {
        long   n_count;
        char   elem_str[1024];
        double e_count;

        long total_count = 0;
        for(int i=0; i<nGrps; i++) {
            get_vrel_size(group_next[i], &n_count, &e_count, elem_str, sizeof(elem_str));
            Print(infoLong, "group_next[%d]: %ld nodes", i, n_count);
            total_count += n_count;
        }
        Print(infoLong, "group_next: %ld nodes total", total_count);
    }

    if (files[2] != NULL)
        do_output(files[2], visited);
    HREexit (LTSMIN_EXIT_SUCCESS);
}
