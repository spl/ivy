# Makefile for yices_sover_test.ml
# 


ifndef ARCHOS
  ARCHOS = x86_LINUX
endif

all:
	$(MAKE) yices_solver_test
	$(MAKE) yices_solver_test NATIVECAML=1

#
# If you've done a 'make install' with cvc lite, then
# the defaults below should work. Otherwise setting the
# environment variables as below should work.
#
# for example on a x86 linux machine
# YICESLIB = /path/to/yices/lib
# YICESINC = /path/to/yices/include
#
ifndef YICESLIB
  CVCLLIB = /usr/local/lib
endif
ifndef YICESINC
  CVCLINC = /usr/local/include
endif
ifndef OCAMLINC
  OCAMLINC = /usr/lib/ocaml
endif

OBJDIR = obj/$(ARCHOS)
DEPENDDIR = obj/.depend


SOURCEDIRS = .

MODULES = yices yices_solver_test

COMPILEFLAGS =
LINKFLAGS =


ENDLINKFLAGS = -cclib -L$(YICESLIB) -cclib -lyices -cclib -lstdc++ -cclib -lgmp

CAML_CFLAGS += -ccopt -I$(OCAMLINC) -ccopt -I$(YICESINC)

include ../../../../cil/ocamlutil/Makefile.ocaml

PROJECT_EXECUTABLE = $(OBJDIR)/yices_test$(EXE)
PROJECT_MODULES = $(MODULES)

PROJECT_CMODULES = yices_ocaml_wrappers

PROJECT_LIBS = unix str

$(PROJECT_EXECUTABLE) : $(PROJECT_MODULES:%=$(OBJDIR)/%.$(CMO)) \
                        $(PROJECT_CMODULES:%=$(OBJDIR)/%.$(CMC))
	@$(NARRATIVE) "Linking $(COMPILETOWHAT) $@ $(LINKMSG)"
	$(AT)$(CAMLLINK) -verbose -o $@ \
		$(PROJECT_LIBS:%=%.$(CMXA)) \
		$(PROJECT_MODULES:%=$(OBJDIR)/%.$(CMO)) \
		$(PROJECT_CMODULES:%=$(OBJDIR)/%.$(CMC)) \
		$(ENDLINKFLAGS)

yices_solver_test: $(PROJECT_EXECUTABLE)

clean:
	rm -f $(OBJDIR)/*.* $(DEPENDDIR)/*.*
