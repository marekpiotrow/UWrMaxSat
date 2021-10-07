BUILD_DIR?=build
MAXPRE?=-D MAXPRE
USESCIP?=-D USE_SCIP -pthread
BIGWEIGHTS?=#-D BIG_WEIGHTS
MINISATP_RELSYM?=
MINISATP_REL?=-std=c++11 -O3 -D NDEBUG -Wno-strict-aliasing -D INCREMENTAL -D GLUCOSE4   $(MAXPRE) $(USESCIP) $(BIGWEIGHTS)
MINISATP_DEB?=-std=c++11 -O0 -D DEBUG  -Wno-strict-aliasing -D INCREMENTAL -D GLUCOSE4   $(MAXPRE) $(USESCIP) $(BIGWEIGHTS)
MINISATP_PRF?=-std=c++11 -O3 -D NDEBUG -Wno-strict-aliasing -D INCREMENTAL -D GLUCOSE4   $(MAXPRE) $(USESCIP) $(BIGWEIGHTS)
MINISATP_FPIC?=-fpic
MINISAT_INCLUDE?=-I/include -I/include/minisat -I../glucose-syrup-4.1
MINISAT_LIB?=-L/lib -L../glucose-syrup-4.1/simp -l_release $(USESCIP)
ifneq ($(MAXPRE),)
MCL_INCLUDE?=-I../maxpre/src
MCL_LIB?=-L../maxpre/src/lib -lmaxpre
else
MCL_INCLUDE?=
MCL_LIB?=
endif
ifneq ($(USESCIP),)
MCL_INCLUDE+=-I../scipoptsuite-7.0.3/scip/src -I../scipoptsuite-7.0.3/build/scip
MCL_LIB+=-L../scipoptsuite-7.0.3/build/lib -lscip -lsoplex-pic
endif
prefix?=
