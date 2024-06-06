## TODO ###########################################################################################
#

.PHONY:	r d p sh cr cd cp csh lr ld lp lsh config all install clean \
	distclean
all:	r lr lsh

## Load Previous Configuration ####################################################################

-include config.mk

## Configurable options ###########################################################################

# Directory to store object files, libraries, executables, and dependencies:
BUILD_DIR      ?= build

# Do not include debug-symbols in release builds
MINISATP_RELSYM ?= 

# Do not include --static in MacOS
ifeq ($(shell uname -s),Darwin)
LDFLAG_STATIC =
else
    ifeq ($(OS),Windows_NT)
	LDFLAGS_STATIC=
    else
        LDFLAG_STATIC = --static
    endif
endif

# Sets of compile flags for different build types
MINISATP_REL    ?= -std=c++11 -O3 -D NDEBUG -Wno-strict-aliasing -D COMINISATPS $(MAXPRE) $(BIGWEIGHTS)
MINISATP_DEB    ?= -std=c++11 -O0 -D DEBUG  -Wno-strict-aliasing -D COMINISATPS $(MAXPRE) $(BIGWEIGHTS)
MINISATP_PRF    ?= -std=c++11 -O3 -D NDEBUG -Wno-strict-aliasing -D COMINISATPS $(MAXPRE) $(BIGWEIGHTS)
MINISATP_FPIC   ?= -fpic

# GNU Standard Install Variables
exec_prefix ?= $(prefix)
includedir  ?= $(prefix)/include
bindir      ?= $(exec_prefix)/bin
libdir      ?= $(exec_prefix)/lib
datarootdir ?= $(prefix)/share
mandir      ?= $(datarootdir)/man

# Dependencies
MINISAT_INCLUDE?=-I$(includedir) -I$(includedir)/cominisatps -I../cominisatps
MINISAT_LIB    ?=-L$(libdir) -L../cominisatps/build/release/lib -lcominisatps
MCL_INCLUDE    ?=-I../maxpre/src
MCL_LIB        ?=-L../maxpre/src/lib -lmaxpre

## Write Configuration  ###########################################################################

config:
	@( echo 'BUILD_DIR?=$(BUILD_DIR)'             ; \
           echo 'MAXPRE?=-D MAXPRE'                   ; \
           echo 'USESCIP?=-D USE_SCIP -pthread'       ; \
           echo 'BIGWEIGHTS?=#-D BIG_WEIGHTS'         ; \
	   echo 'MINISATP_RELSYM?=$(MINISATP_RELSYM)'           ; \
	   echo 'MINISATP_REL?=$(MINISATP_REL) $$(MAXPRE) $$(USESCIP) $$(BIGWEIGHTS)' ; \
	   echo 'MINISATP_DEB?=$(MINISATP_DEB) $$(MAXPRE) $$(USESCIP) $$(BIGWEIGHTS)' ; \
	   echo 'MINISATP_PRF?=$(MINISATP_PRF) $$(MAXPRE) $$(USESCIP) $$(BIGWEIGHTS)' ; \
	   echo 'MINISATP_FPIC?=$(MINISATP_FPIC)'               ; \
	   echo 'MINISAT_INCLUDE?=$(MINISAT_INCLUDE)' ; \
	   echo 'MINISAT_LIB?=$(MINISAT_LIB) $$(USESCIP)'         ; \
           echo 'ifneq ($$(MAXPRE),)'                  ; \
	   echo 'MCL_INCLUDE?=$(MCL_INCLUDE)'         ; \
	   echo 'MCL_LIB?=$(MCL_LIB)'                 ; \
           echo 'else'                                ; \
           echo 'MCL_INCLUDE?='                       ; \
           echo 'MCL_LIB?='                           ; \
           echo 'endif'                               ; \
           echo 'ifneq ($$(USESCIP),)'                  ; \
	   echo 'MCL_INCLUDE+=-I../scipoptsuite-8.1.0/scip/src -I../scipoptsuite-8.1.0/build/scip' ; \
	   echo 'MCL_LIB+=-L../scipoptsuite-8.1.0/build/lib -lscip -lsoplex-pic'                 ; \
           echo 'endif'                                ; \
	   echo 'prefix?=$(prefix)'                   ) > config.mk

## Configurable options end #######################################################################

INSTALL ?= install

# Target file names
MINISATP      = uwrmaxsat#  Name of MiniSat+ main executable.
MINISATP_SLIB = libuwrmaxsat.a#  Name of MiniSat+ static library.
MINISATP_DLIB = libuwrmaxsat.so# Name of MiniSat+ shared library.

# Shared Library Version
SOMAJOR=1
SOMINOR=6
SORELEASE?=.1#   Declare empty to leave out from library file name.

MINISATP_CXXFLAGS = -IADTs -include Global.h -include Main.h -D_FILE_OFFSET_BITS=64 -D __STDC_LIMIT_MACROS -Wall -Wno-parentheses -Wextra  $(MCL_INCLUDE) $(MINISAT_INCLUDE)
MINISATP_LDFLAGS  = -Wall  $(MCL_LIB) $(MINISAT_LIB) -lz -lgmp

ifeq ($(VERB),)
ECHO=@
VERB=@
else
ECHO=#
VERB=
endif

SRCS = $(wildcard *.cc) $(wildcard ADTs/*.cc)
HDRS = $(wildcard *.h)
OBJS = $(filter-out %Main.o, $(SRCS:.cc=.o))

r:	$(BUILD_DIR)/release/bin/$(MINISATP)
d:	$(BUILD_DIR)/debug/bin/$(MINISATP)
p:	$(BUILD_DIR)/profile/bin/$(MINISATP)
sh:	$(BUILD_DIR)/dynamic/bin/$(MINISATP)

lr:	$(BUILD_DIR)/release/lib/$(MINISATP_SLIB)
ld:	$(BUILD_DIR)/debug/lib/$(MINISATP_SLIB)
lp:	$(BUILD_DIR)/profile/lib/$(MINISATP_SLIB)
lsh:	$(BUILD_DIR)/dynamic/lib/$(MINISATP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE)

## Build-type Compile-flags:
$(BUILD_DIR)/release/%.o:			MINISATP_CXXFLAGS +=$(MINISATP_REL) $(MINISATP_RELSYM)
$(BUILD_DIR)/debug/%.o:				MINISATP_CXXFLAGS +=$(MINISATP_DEB) -g
$(BUILD_DIR)/profile/%.o:			MINISATP_CXXFLAGS +=$(MINISATP_PRF) -pg
$(BUILD_DIR)/dynamic/%.o:			MINISATP_CXXFLAGS +=$(MINISATP_REL) $(MINISATP_FPIC)

## Build-type Link-flags:
$(BUILD_DIR)/profile/bin/$(MINISATP):		MINISATP_LDFLAGS += -pg
$(BUILD_DIR)/release/bin/$(MINISATP):		MINISATP_LDFLAGS += $(LDFLAG_STATIC) $(MINISATP_RELSYM)
$(BUILD_DIR)/debug/bin/$(MINISATP):	        MINISATP_LDFLAGS += $(LDFLAG_STATIC)

## Executable dependencies
$(BUILD_DIR)/release/bin/$(MINISATP):	 	$(BUILD_DIR)/release/Main.o $(BUILD_DIR)/release/lib/$(MINISATP_SLIB)
$(BUILD_DIR)/debug/bin/$(MINISATP):	 	$(BUILD_DIR)/debug/Main.o $(BUILD_DIR)/debug/lib/$(MINISATP_SLIB)
$(BUILD_DIR)/profile/bin/$(MINISATP):	 	$(BUILD_DIR)/profile/Main.o $(BUILD_DIR)/profile/lib/$(MINISATP_SLIB)
# need the main-file be compiled with fpic?
$(BUILD_DIR)/dynamic/bin/$(MINISATP):	 	$(BUILD_DIR)/dynamic/Main.o $(BUILD_DIR)/dynamic/lib/$(MINISATP_DLIB)

## Library dependencies
$(BUILD_DIR)/release/lib/$(MINISATP_SLIB):	$(foreach o,$(OBJS),$(BUILD_DIR)/release/$(o))
$(BUILD_DIR)/debug/lib/$(MINISATP_SLIB):	$(foreach o,$(OBJS),$(BUILD_DIR)/debug/$(o))
$(BUILD_DIR)/profile/lib/$(MINISATP_SLIB):	$(foreach o,$(OBJS),$(BUILD_DIR)/profile/$(o))
$(BUILD_DIR)/dynamic/lib/$(MINISATP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE):	$(foreach o,$(OBJS),$(BUILD_DIR)/dynamic/$(o))

## Compile rules (these should be unified, buit I have not yet found a way which works in GNU Make)
$(BUILD_DIR)/release/%.o:	%.cc
	$(ECHO) echo Compiling: $@
	$(VERB) mkdir -p $(dir $@) $(dir $(BUILD_DIR)/dep/$*.d)
	$(VERB) $(CXX) $(MINISATP_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/dep/$*.d

$(BUILD_DIR)/profile/%.o:	%.cc
	$(ECHO) echo Compiling: $@
	$(VERB) mkdir -p $(dir $@) $(dir $(BUILD_DIR)/dep/$*.d)
	$(VERB) $(CXX) $(MINISATP_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/dep/$*.d

$(BUILD_DIR)/debug/%.o:	%.cc
	$(ECHO) echo Compiling: $@
	$(VERB) mkdir -p $(dir $@) $(dir $(BUILD_DIR)/dep/$*.d)
	$(VERB) $(CXX) $(MINISATP_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/dep/$*.d

$(BUILD_DIR)/dynamic/%.o:	%.cc
	$(ECHO) echo Compiling: $@
	$(VERB) mkdir -p $(dir $@) $(dir $(BUILD_DIR)/dep/$*.d)
	$(VERB) $(CXX) $(MINISATP_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/dep/$*.d

## Linking rule
$(BUILD_DIR)/release/bin/$(MINISATP) $(BUILD_DIR)/debug/bin/$(MINISATP) $(BUILD_DIR)/profile/bin/$(MINISATP) $(BUILD_DIR)/dynamic/bin/$(MINISATP):
	$(ECHO) echo Linking Binary: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $^ $(MINISATP_LDFLAGS) $(LDFLAGS) -o $@

## Static Library rule
%/lib/$(MINISATP_SLIB):
	$(ECHO) echo Linking Static Library: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(AR) -rcs $@ $^

## Shared Library rule
$(BUILD_DIR)/dynamic/lib/$(MINISATP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE)\
 $(BUILD_DIR)/dynamic/lib/$(MINISATP_DLIB).$(SOMAJOR)\
 $(BUILD_DIR)/dynamic/lib/$(MINISATP_DLIB):
	$(ECHO) echo Linking Shared Library: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) -o $@ -shared -Wl,-soname,$(MINISATP_DLIB).$(SOMAJOR) $^ $(MINISATP_LDFLAGS) 
	$(VERB) ln -sf $(MINISATP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE) $(BUILD_DIR)/dynamic/lib/$(MINISATP_DLIB).$(SOMAJOR)
	$(VERB) ln -sf $(MINISATP_DLIB).$(SOMAJOR) $(BUILD_DIR)/dynamic/lib/$(MINISATP_DLIB)

install:	install-bin

install-bin: $(BUILD_DIR)/release/bin/$(MINISATP)
	$(INSTALL) -d $(DESTDIR)$(bindir)
	$(INSTALL) $(BUILD_DIR)/release/bin/$(MINISATP) $(DESTDIR)$(bindir)/

clean:
	rm -f $(foreach t, release debug profile dynamic, $(foreach o, $(SRCS:.cc=.o), $(BUILD_DIR)/$t/$o)) \
	  $(foreach d, $(SRCS:.cc=.d), $(BUILD_DIR)/dep/$d) \
	  $(foreach t, release debug profile dynamic, $(BUILD_DIR)/$t/bin/$(MINISATP)) \
	  $(foreach t, release debug profile, $(BUILD_DIR)/$t/lib/$(MINISATP_SLIB)) \
	  $(BUILD_DIR)/dynamic/lib/$(MINISATP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE)

distclean:	clean
	rm -f config.mk

## Include generated dependencies
## NOTE: dependencies are assumed to be the same in all build modes at the moment!
-include $(foreach s, $(SRCS:.cc=.d), $(BUILD_DIR)/dep/$s)
