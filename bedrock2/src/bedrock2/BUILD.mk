BEDROCK_DIR := $(patsubst %/,%,$(dir $(lastword $(MAKEFILE_LIST))))
BEDROCK_VFILES := $(call rwildcard,$(BEDROCK_DIR),*.v)
BEDROCK_COQDEPFLAGS := -Q $(BEDROCK_DIR) $(notdir $(BEDROCK_DIR))
BEDROCK_REQUIREFLAGS := -Q $(O)/$(BEDROCK_DIR) $(notdir $(BEDROCK_DIR))

BEDROCK_COQFLAGS := $(COQUTIL_REQUIREFLAGS) $(BEDROCK_REQUIREFLAGS) -w -deprecated-from-Coq,-deprecated-since-9.0,-deprecated-since-8.20
$(O)/$(BEDROCK_DIR)/%.vo: private COQFLAGS += $(BEDROCK_COQFLAGS)
$(O)/$(BEDROCK_DIR)/%.vos: private COQFLAGS += $(BEDROCK_COQFLAGS)
$(O)/$(BEDROCK_DIR)/%.vok: private COQFLAGS += $(BEDROCK_COQFLAGS)
$(BEDROCK_DIR)/_CoqProject: private COQFLAGS += $(BEDROCK_COQFLAGS)
