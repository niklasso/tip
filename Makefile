## TODO ###########################################################################################
#

.PHONY:	r d p sh cr cd cp csh lr ld lp lsh config all install install-headers install-lib clean \
	distclean
all:	r lr lsh

## Load Previous Configuration ####################################################################

-include config.mk

## Configurable options ###########################################################################

# Directory to store object files, libraries, executables, and dependencies:
BUILD_DIR      ?= build

# Include debug-symbols in release builds
TIP_RELSYM ?= -g

# Sets of compile flags for different build types
TIP_REL    ?= -O3 -D NDEBUG
TIP_DEB    ?= -O0 -D DEBUG 
TIP_PRF    ?= -O3 -D NDEBUG
TIP_FPIC   ?= -fpic

# Dependencies
MINISAT_INCLUDE?=
MINISAT_LIB    ?=-lminisat
MCL_INCLIDE    ?=
MCL_LIB        ?=-lmcl

# GNU Standard Install Prefix
prefix         ?= /usr/local

## Write Configuration  ###########################################################################

config:
	@( echo 'BUILD_DIR?=$(BUILD_DIR)'             ; \
	   echo 'TIP_RELSYM?=$(TIP_RELSYM)'           ; \
	   echo 'TIP_REL?=$(TIP_REL)'                 ; \
	   echo 'TIP_DEB?=$(TIP_DEB)'                 ; \
	   echo 'TIP_PRF?=$(TIP_PRF)'                 ; \
	   echo 'TIP_FPIC?=$(TIP_FPIC)'               ; \
	   echo 'MINISAT_INCLUDE?=$(MINISAT_INCLUDE)' ; \
	   echo 'MINISAT_LIB?=$(MINISAT_LIB)'         ; \
	   echo 'MCL_INCLUDE?=$(MCL_INCLUDE)'         ; \
	   echo 'MCL_LIB?=$(MCL_LIB)'                 ; \
	   echo 'prefix?=$(prefix)'                   ) > config.mk

## Configurable options end #######################################################################

INSTALL ?= install

# GNU Standard Install Variables
exec_prefix ?= $(prefix)
includedir  ?= $(prefix)/include
bindir      ?= $(exec_prefix)/bin
libdir      ?= $(exec_prefix)/lib
datarootdir ?= $(prefix)/share
mandir      ?= $(datarootdir)/man

# Target file names
TIP      = tip#       Name of Tip main executable.
TIP_SLIB = libtip.a#  Name of Tip static library.
TIP_DLIB = libtip.so# Name of Tip shared library.

# Shared Library Version
SOMAJOR=1
SOMINOR=0
SORELEASE?=.0#   Declare empty to leave out from library file name.

TIP_CXXFLAGS = -I. -I.. -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -Wall -Wno-parentheses -Wextra  $(MCL_INCLUDE) $(MINISAT_INCLUDE)
TIP_LDFLAGS  = -Wall  $(MCL_LIB) $(MINISAT_LIB) -lz

ifeq ($(VERB),)
ECHO=@
VERB=@
else
ECHO=#
VERB=
endif

SRCS = $(wildcard tip/*.cc) $(wildcard tip/*/*.cc)
HDRS = $(wildcard tip/*.h) $(wildcard tip/*/*.h)
OBJS = $(filter-out %Main.o, $(SRCS:.cc=.o))

r:	$(BUILD_DIR)/release/bin/$(TIP)
d:	$(BUILD_DIR)/debug/bin/$(TIP)
p:	$(BUILD_DIR)/profile/bin/$(TIP)
sh:	$(BUILD_DIR)/dynamic/bin/$(TIP)

lr:	$(BUILD_DIR)/release/lib/$(TIP_SLIB)
ld:	$(BUILD_DIR)/debug/lib/$(TIP_SLIB)
lp:	$(BUILD_DIR)/profile/lib/$(TIP_SLIB)
lsh:	$(BUILD_DIR)/dynamic/lib/$(TIP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE)

## Build-type Compile-flags:
$(BUILD_DIR)/release/%.o:			TIP_CXXFLAGS +=$(TIP_REL) $(TIP_RELSYM)
$(BUILD_DIR)/debug/%.o:				TIP_CXXFLAGS +=$(TIP_DEB) -g
$(BUILD_DIR)/profile/%.o:			TIP_CXXFLAGS +=$(TIP_PRF) -pg
$(BUILD_DIR)/dynamic/%.o:			TIP_CXXFLAGS +=$(TIP_REL) $(TIP_FPIC)

## Build-type Link-flags:
$(BUILD_DIR)/profile/bin/$(TIP):		TIP_LDFLAGS += -pg
$(BUILD_DIR)/release/bin/$(TIP):		TIP_LDFLAGS += --static $(TIP_RELSYM)
$(BUILD_DIR)/debug/bin/$(TIP):		        TIP_LDFLAGS += --static

## Executable dependencies
$(BUILD_DIR)/release/bin/$(TIP):	 	$(BUILD_DIR)/release/tip/Main.o $(BUILD_DIR)/release/lib/$(TIP_SLIB)
$(BUILD_DIR)/debug/bin/$(TIP):	 		$(BUILD_DIR)/debug/tip/Main.o $(BUILD_DIR)/debug/lib/$(TIP_SLIB)
$(BUILD_DIR)/profile/bin/$(TIP):	 	$(BUILD_DIR)/profile/tip/Main.o $(BUILD_DIR)/profile/lib/$(TIP_SLIB)
# need the main-file be compiled with fpic?
$(BUILD_DIR)/dynamic/bin/$(TIP):	 	$(BUILD_DIR)/dynamic/tip/Main.o $(BUILD_DIR)/dynamic/lib/$(TIP_DLIB)

## Library dependencies
$(BUILD_DIR)/release/lib/$(TIP_SLIB):	$(foreach o,$(OBJS),$(BUILD_DIR)/release/$(o))
$(BUILD_DIR)/debug/lib/$(TIP_SLIB):		$(foreach o,$(OBJS),$(BUILD_DIR)/debug/$(o))
$(BUILD_DIR)/profile/lib/$(TIP_SLIB):	$(foreach o,$(OBJS),$(BUILD_DIR)/profile/$(o))
$(BUILD_DIR)/dynamic/lib/$(TIP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE):	$(foreach o,$(OBJS),$(BUILD_DIR)/dynamic/$(o))

## Compile rules (these should be unified, buit I have not yet found a way which works in GNU Make)
$(BUILD_DIR)/release/%.o:	%.cc
	$(ECHO) echo Compiling: $@
	$(VERB) mkdir -p $(dir $@) $(dir $(BUILD_DIR)/dep/$*.d)
	$(VERB) $(CXX) $(TIP_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/dep/$*.d

$(BUILD_DIR)/profile/%.o:	%.cc
	$(ECHO) echo Compiling: $@
	$(VERB) mkdir -p $(dir $@) $(dir $(BUILD_DIR)/dep/$*.d)
	$(VERB) $(CXX) $(TIP_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/dep/$*.d

$(BUILD_DIR)/debug/%.o:	%.cc
	$(ECHO) echo Compiling: $@
	$(VERB) mkdir -p $(dir $@) $(dir $(BUILD_DIR)/dep/$*.d)
	$(VERB) $(CXX) $(TIP_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/dep/$*.d

$(BUILD_DIR)/dynamic/%.o:	%.cc
	$(ECHO) echo Compiling: $@
	$(VERB) mkdir -p $(dir $@) $(dir $(BUILD_DIR)/dep/$*.d)
	$(VERB) $(CXX) $(TIP_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/dep/$*.d

## Linking rule
$(BUILD_DIR)/release/bin/$(TIP) $(BUILD_DIR)/debug/bin/$(TIP) $(BUILD_DIR)/profile/bin/$(TIP) $(BUILD_DIR)/dynamic/bin/$(TIP):
	$(ECHO) echo Linking Binary: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $^ $(TIP_LDFLAGS) $(LDFLAGS) -o $@

## Static Library rule
%/lib/$(TIP_SLIB):
	$(ECHO) echo Linking Static Library: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(AR) -rcs $@ $^

## Shared Library rule
$(BUILD_DIR)/dynamic/lib/$(TIP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE)\
 $(BUILD_DIR)/dynamic/lib/$(TIP_DLIB).$(SOMAJOR)\
 $(BUILD_DIR)/dynamic/lib/$(TIP_DLIB):
	$(ECHO) echo Linking Shared Library: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $(TIP_LDFLAGS) -o $@ -shared -Wl,-soname,$(TIP_DLIB).$(SOMAJOR) $^
	$(VERB) ln -sf $(TIP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE) $(BUILD_DIR)/dynamic/lib/$(TIP_DLIB).$(SOMAJOR)
	$(VERB) ln -sf $(TIP_DLIB).$(SOMAJOR) $(BUILD_DIR)/dynamic/lib/$(TIP_DLIB)

install:	install-headers install-lib install-bin

install-bin: $(BUILD_DIR)/release/bin/$(TIP)
	$(INSTALL) -d $(DESTDIR)$(bindir)
	$(INSTALL) $(BUILD_DIR)/release/bin/$(TIP) $(DESTDIR)$(bindir)/


install-headers:
#       Create directories
	$(INSTALL) -d $(DESTDIR)$(includedir)/tip
#       Install headers
	for h in $(HDRS) ; do \
	  $(INSTALL) -m 644 $$h $(DESTDIR)$(includedir)/$$h ; \
	done

install-lib: $(BUILD_DIR)/release/lib/$(TIP_SLIB) $(BUILD_DIR)/dynamic/lib/$(TIP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE)
	$(INSTALL) -d $(DESTDIR)$(libdir)
	$(INSTALL) -m 644 $(BUILD_DIR)/dynamic/lib/$(TIP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE) $(DESTDIR)$(libdir)
	ln -sf $(DESTDIR)$(libdir)/$(TIP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE) $(DESTDIR)$(libdir)/$(TIP_DLIB).$(SOMAJOR)
	ln -sf $(DESTDIR)$(libdir)/$(TIP_DLIB).$(SOMAJOR) $(DESTDIR)$(libdir)/$(TIP_DLIB)
	$(INSTALL) -m 644 $(BUILD_DIR)/release/lib/$(TIP_SLIB) $(DESTDIR)$(libdir)

clean:
	rm -f $(foreach t, release debug profile dynamic, $(foreach o, $(SRCS:.cc=.o), $(BUILD_DIR)/$t/$o)) \
	  $(foreach d, $(SRCS:.cc=.d), $(BUILD_DIR)/dep/$d) \
	  $(foreach t, release debug profile dynamic, $(BUILD_DIR)/$t/bin/$(TIP)) \
	  $(foreach t, release debug profile, $(BUILD_DIR)/$t/lib/$(TIP_SLIB)) \
	  $(BUILD_DIR)/dynamic/lib/$(TIP_DLIB).$(SOMAJOR).$(SOMINOR)$(SORELEASE)

distclean:	clean
	rm -f config.mk

## Include generated dependencies
## NOTE: dependencies are assumed to be the same in all build modes at the moment!
-include $(foreach s, $(SRCS:.cc=.d), $(BUILD_DIR)/dep/$s)
