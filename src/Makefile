FRAMAC_SHARE  = /usr/local/share/frama-c
FRAMAC_LIBDIR = $(shell frama-c -print-lib-path)

PLUGIN_NAME     := GamaSlicer
PLUGIN_CMO      := vcgen

VERBOSEMAKE=yes

#WHYLIB := /Users/jpinheiro/.opam/system/lib/why3
WHYLIB := /usr/local/lib/ocaml/4.01.0/why3
SHELL := /bin/bash

PLUGIN_EXTRA_BYTE:= $(WHYLIB)/why3.cma
PLUGIN_EXTRA_OPT:= $(WHYLIB)/why3.cmxa
PLUGIN_BFLAGS:= -I $(WHYLIB)
PLUGIN_OFLAGS:= -I $(WHYLIB)
PLUGIN_LINK_BFLAGS:= -I $(WHYLIB)
PLUGIN_LINK_OFLAGS:= -I $(WHYLIB)


$(addsuffix .cmo, $(PLUGIN_CMO)): $(WHYLIB)/why3.cmi
$(addsuffix .cmx, $(PLUGIN_CMO)): $(WHYLIB)/why3.cmi $(WHYLIB)/why3.cmx

include $(FRAMAC_SHARE)/Makefile.dynamic