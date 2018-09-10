#
# Unix/Linux makefile
# Abulhair Saparov
#

#
# List of source files
#

PCFG_INDUCTION_CPP_SRCS=pcfg_induction.cpp
PCFG_INDUCTION_DBG_OBJS=$(PCFG_INDUCTION_CPP_SRCS:.cpp=.debug.o)
PCFG_INDUCTION_OBJS=$(PCFG_INDUCTION_CPP_SRCS:.cpp=.release.o)

MATH_INDUCTION_CPP_SRCS=math_induction.cpp
MATH_INDUCTION_DBG_OBJS=$(MATH_INDUCTION_CPP_SRCS:.cpp=.debug.o)
MATH_INDUCTION_OBJS=$(MATH_INDUCTION_CPP_SRCS:.cpp=.release.o)


#
# Compile and link options
#

LIBRARY_PKG_LIBS=
PKG_LIBS=-Wl,--no-as-needed -lpthread
GLIBC := $(word 2,$(shell getconf GNU_LIBC_VERSION))
GLIBC_HAS_RT := $(shell expr $(GLIBC) \>= 2.17)
ifeq "$(GLIBC_HAS_RT)" "0"
	LIBRARY_PKG_LIBS += -lrt
	PKG_LIBS += -lrt
endif

CPP=g++
WARNING_FLAGS=-Wall -Wpedantic
override CPPFLAGS_DBG += $(WARNING_FLAGS) -I. -g -march=native -std=c++11 $(PKG_LIBS)
override CPPFLAGS += $(WARNING_FLAGS) -I. -O3 -DNDEBUG -march=native -std=c++11 -fno-stack-protector $(PKG_LIBS)
override LDFLAGS_DBG += -g $(LIB_PATHS)
override LDFLAGS += $(LIB_PATHS) -fwhole-program


#
# Compile command
#

-include $(PCFG_INDUCTION_OBJS:.release.o=.release.d)
-include $(PCFG_INDUCTION_DBG_OBJS:.debug.o=.debug.d)
-include $(MATH_INDUCTION_OBJS:.release.o=.release.d)
-include $(MATH_INDUCTION_DBG_OBJS:.debug.o=.debug.d)

define make_dependencies
	$(1) $(2) -c $(3).$(4) -o $(3).$(5).o
	$(1) -MM $(2) $(3).$(4) > $(3).$(5).d
	@mv -f $(3).$(5).d $(3).$(5).d.tmp
	@sed -e 's|.*:|$(3).$(5).o:|' < $(3).$(5).d.tmp > $(3).$(5).d
	@sed -e 's/.*://' -e 's/\\$$//' < $(3).$(5).d.tmp | fmt -1 | \
		sed -e 's/^ *//' -e 's/$$/:/' >> $(3).$(5).d
	@rm -f $(3).$(5).d.tmp
endef

%.release.o: %.cpp
	$(call make_dependencies,$(CPP),$(CPPFLAGS),$*,cpp,release)
%.release.pic.o: %.cpp
	$(call make_dependencies,$(CPP),$(CPPFLAGS),$*,cpp,release.pic)
%.debug.o: %.cpp
	$(call make_dependencies,$(CPP),$(CPPFLAGS_DBG),$*,cpp,debug)
%.debug.pic.o: %.cpp
	$(call make_dependencies,$(CPP),$(CPPFLAGS_DBG),$*,cpp,debug.pic)


#
# GNU Make: targets that don't build files
#

.PHONY: all debug clean distclean

#
# Make targets
#

all: pcfg_induction

debug: pcfg_induction_dbg

pcfg_induction: $(LIBS) $(PCFG_INDUCTION_OBJS)
		$(CPP) -o pcfg_induction $(CPPFLAGS) $(LDFLAGS) $(PCFG_INDUCTION_OBJS)

pcfg_induction_dbg: $(LIBS) $(PCFG_INDUCTION_DBG_OBJS)
		$(CPP) -o pcfg_induction_dbg $(CPPFLAGS_DBG) $(LDFLAGS_DBG) $(PCFG_INDUCTION_DBG_OBJS)

math_induction: $(LIBS) $(MATH_INDUCTION_OBJS)
		$(CPP) -o math_induction $(CPPFLAGS) $(LDFLAGS) $(MATH_INDUCTION_OBJS)

math_induction_dbg: $(LIBS) $(MATH_INDUCTION_DBG_OBJS)
		$(CPP) -o math_induction_dbg $(CPPFLAGS_DBG) $(LDFLAGS_DBG) $(MATH_INDUCTION_DBG_OBJS)

clean:
	    ${RM} -f *.o */*.o */*/*.o *.d */*.d */*/*.d pcfg_induction pcfg_induction.exe pcfg_induction_dbg pcfg_induction_dbg.exe math_induction math_induction.exe math_induction_dbg math_induction_dbg.exe $(LIBS)

distclean:  clean
	    ${RM} -f *~
