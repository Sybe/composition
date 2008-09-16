#ifndef LTSMETA_H
#define LTSMETA_H

#include "config.h"
#include "stream.h"
#include <stdint.h>
#include "data_io.h"

typedef struct lts_meta_s *lts_t;
typedef uint64_t lts_state_t;


extern void lts_set_root(lts_t lts,lts_state_t state);
extern lts_state_t lts_get_root(lts_t lts);

extern void lts_set_trans(lts_t lts,uint64_t count);
extern uint64_t lts_get_trans(lts_t lts);

extern void lts_set_states(lts_t lts,uint64_t count);
extern uint64_t lts_get_states(lts_t lts);

extern void lts_set_labels(lts_t lts,uint64_t count);
extern uint64_t lts_get_labels(lts_t lts);

extern int lts_has_tau(lts_t lts);
extern void lts_set_tau(lts_t lts,uint64_t tau);
extern uint64_t lts_get_tau(lts_t lts);

extern void lts_set_comment(lts_t lts,char*comment);
extern char* lts_get_comment(lts_t lts);

extern lts_t lts_create();

typedef enum {DIR_INFO} info_fmt_t;
extern void lts_write_info(lts_t lts,data_stream_t ds,info_fmt_t format);
extern lts_t lts_read(data_stream_t ds);

#endif
