# Makefile for cvcl_sover_test.ml
# 


ifndef ARCHOS
  ARCHOS = x86_LINUX
endif

all:
	$(MAKE) cvcl_solver_test
	$(MAKE) cvcl_solver_test NATIVECAML=1

#
# If you've done a 'make install' with cvc lite, then
# the defaults below should work. Otherwise setting the
# environment variables as below should work.
#
# for example on a x86 linux machine
# CVCLLIB = /path/to/cvcl/lib/linux-i686
# CVCLINC = /path/to/cvcl/src/include
#
ifndef CVCLLIB
  CVCLLIB = /usr/local/lib
endif
ifndef CVCLINC
  CVCLINC = /usr/local/include
endif
ifndef OCAMLINC
  OCAMLINC = /usr/lib/ocaml
endif

OBJDIR = obj/$(ARCHOS)
DEPENDDIR = obj/.depend


SOURCEDIRS = .

MODULES = cvcl cvcl_solver_test

COMPILEFLAGS =
LINKFLAGS =


ENDLINKFLAGS = -cclib -L$(CVCLLIB) -cclib -lcvclite -cclib -lstdc++ -cclib -lgmp

CAML_CFLAGS += -ccopt -I$(OCAMLINC) -ccopt -I$(CVCLINC)

include ../../../../cil/ocamlutil/Makefile.ocaml

PROJECT_EXECUTABLE = $(OBJDIR)/cvcl_test$(EXE)
PROJECT_MODULES = $(MODULES)

PROJECT_CMODULES = cvcl_ocaml_wrappers

PROJECT_LIBS = unix str

$(PROJECT_EXECUTABLE) : $(PROJECT_MODULES:%=$(OBJDIR)/%.$(CMO)) \
                        $(PROJECT_CMODULES:%=$(OBJDIR)/%.$(CMC))
	@$(NARRATIVE) "Linking $(COMPILETOWHAT) $@ $(LINKMSG)"
	$(AT)$(CAMLLINK) -verbose -o $@ \
		$(PROJECT_LIBS:%=%.$(CMXA)) \
		$(PROJECT_MODULES:%=$(OBJDIR)/%.$(CMO)) \
		$(PROJECT_CMODULES:%=$(OBJDIR)/%.$(CMC)) \
		$(ENDLINKFLAGS)

cvcl_solver_test: $(PROJECT_EXECUTABLE)

clean:
	rm -f $(OBJDIR)/*.* $(DEPENDDIR)/*.*
