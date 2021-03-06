HRE_LIB = ../hre/libhre.la
SEQ_CPPFLAGS = $(AM_CPPFLAGS)
PINS_LIBS  =
PINS_LIBS += ../mc-lib/libmc.la
PINS_LIBS += ../lts-io/liblts-io.la
PINS_LIBS += ../hre-io/libhre-io.la
PINS_LIBS += $(HRE_LIB)
PINS_LIBS += ../pins-lib/libpins.la
PINS_LIBS += ../ltsmin-lib/libltsmin.la
PINS_LIBS += ../util-lib/libutil.la
PINS_LIBS += ../dm/libdm.la
VSET_LIBS = ../vset-lib/libvset.la

bin_PROGRAMS = etf2lts-seq pins2lts-seq

if HAVE_LIBSTEP_INFO
bin_PROGRAMS += lpo2lts-seq
endif

if HAVE_LIBMCRL2
bin_PROGRAMS += lps2lts-seq
endif

if HAVE_LIBPBES
bin_PROGRAMS += pbes2lts-seq
endif

if HAVE_DVE
bin_PROGRAMS += dve2lts-seq
endif

if HAVE_SPINS
bin_PROGRAMS += prom2lts-seq
endif

#bin_PROGRAMS += mapa2lts-seq

# pins2lts-seq
pins2lts_seq_SOURCES   = pins2lts-seq.c
pins2lts_seq_SOURCES  += ../pins-lib/dlopen-pins.c ../pins-lib/dlopen-pins.h
pins2lts_seq_LDADD     = $(HRE_LIB) $(PINS_LIBS)
pins2lts_seq_LDADD    += $(VSET_LIBS)
pins2lts_seq_CPPFLAGS  = -DPINS_DLL $(SEQ_CPPFLAGS)
if !BUILD_OS_IS_DARWIN
pins2lts_seq_LDFLAGS   = -Wl,-E
endif
nodist_EXTRA_pins2lts_seq_SOURCES = automake-force-linker.cxx # req. by vset


# etf2lts-seq
etf2lts_seq_SOURCES   = pins2lts-seq.c
etf2lts_seq_SOURCES  += ../pins-lib/etf-pins.c ../pins-lib/etf-pins.h
etf2lts_seq_LDADD     = $(HRE_LIB) $(PINS_LIBS)
etf2lts_seq_LDADD    += $(VSET_LIBS)
etf2lts_seq_CPPFLAGS  = -DETF $(SEQ_CPPFLAGS)
nodist_EXTRA_etf2lts_seq_SOURCES = automake-force-linker.cxx # req. by vset

# lpo2lts-seq
lpo2lts_seq_SOURCES   = pins2lts-seq.c
lpo2lts_seq_LDADD     = $(HRE_LIB) $(PINS_LIBS) ../pins-lib/libmcrl-pins.la
lpo2lts_seq_LDADD    += $(VSET_LIBS) $(MCRL_LIBS)
lpo2lts_seq_CPPFLAGS  = -DMCRL $(MCRL_CPPFLAGS) $(SEQ_CPPFLAGS)
lpo2lts_seq_LDFLAGS   = $(MCRL_LDFLAGS) $(AM_LDFLAGS)
nodist_EXTRA_lpo2lts_seq_SOURCES = automake-force-linker.cxx #req. by mcrl

# lps2lts-seq
lps2lts_seq_SOURCES   = pins2lts-seq.c
lps2lts_seq_LDADD     = $(HRE_LIB) $(PINS_LIBS)
lps2lts_seq_LDADD    += $(VSET_LIBS) ../pins-lib/libmcrl2-pins.la
lps2lts_seq_CPPFLAGS  = -DMCRL2 $(SEQ_CPPFLAGS)
lps2lts_seq_LDFLAGS   = $(MCRL2_LDFLAGS) $(AM_LDFLAGS)
nodist_EXTRA_lps2lts_seq_SOURCES = automake-force-linker.cxx #req. by mcrl2s

# pbes2lts-seq
pbes2lts_seq_SOURCES   = pins2lts-seq.c
pbes2lts_seq_LDADD     = $(HRE_LIB) $(PINS_LIBS)
pbes2lts_seq_LDADD    += $(VSET_LIBS) ../pins-lib/libpbes-pins.la
pbes2lts_seq_CPPFLAGS  = -DLTSMIN_PBES $(SEQ_CPPFLAGS)
pbes2lts_seq_LDFLAGS   = $(MCRL2_LDFLAGS) $(AM_LDFLAGS)
nodist_EXTRA_pbes2lts_seq_SOURCES = automake-force-linker.cxx #req. by pbes

# dve2lts-seq
dve2lts_seq_SOURCES   = pins2lts-seq.c
dve2lts_seq_SOURCES  += ../pins-lib/dve-pins.c ../pins-lib/dve-pins.h
dve2lts_seq_LDADD     = $(HRE_LIB) $(PINS_LIBS)
dve2lts_seq_LDADD    += $(VSET_LIBS) $(DVEC_LIBS)
dve2lts_seq_CPPFLAGS  = -DDIVINE $(DIVINE_CPPFLAGS) $(SEQ_CPPFLAGS)
dve2lts_seq_LDFLAGS   = $(DIVINE_LDFLAGS) $(AM_LDFLAGS)
nodist_EXTRA_dve2lts_seq_SOURCES = automake-force-linker.cxx # req. by vset

# prom2lts-seq
prom2lts_seq_SOURCES  = pins2lts-seq.c
prom2lts_seq_SOURCES += ../pins-lib/prom-pins.c ../pins-lib/prom-pins.h
prom2lts_seq_LDADD    = $(HRE_LIB) $(PINS_LIBS)
prom2lts_seq_LDADD   += $(VSET_LIBS) $(SPINS_LIBS)
prom2lts_seq_CPPFLAGS = -DSPINS $(SPINS_CPPFLAGS) $(SEQ_CPPFLAGS)
prom2lts_seq_LDFLAGS  = $(SPINS_LDFLAGS) $(AM_LDFLAGS)
nodist_EXTRA_prom2lts_seq_SOURCES = automake-force-linker.cxx # req. by vset

# mapa2lts-seq
mapa2lts_seq_SOURCES   = pins2lts-seq.c
mapa2lts_seq_LDADD     = $(HRE_LIB)
mapa2lts_seq_LDADD    += ../pins-lib/libmapa-pins.la -lscoop
mapa2lts_seq_LDADD    += $(PINS_LIBS) $(VSET_LIBS)
mapa2lts_seq_LDFLAGS   = $(MAPA_LD_FLAGS) $AD_LDFLAGS
mapa2lts_seq_CPPFLAGS  = -DMAPA $(SEQ_CPPFLAGS)
nodist_EXTRA_mapa2lts_seq_SOURCES = automake-force-linker.cxx # req. by vset

