SPHINXOPTS   ?=
SPHINXBUILD  ?= sphinx-build
SOURCEDIR     = source.template
GENDIR        = source
BUILDDIR     ?= build
ROOTDIR      ?= work

all: clean html

# Sources
SOURCES = $(wildcard $(SOURCEDIR)/*.md)

# Generate sources
$(GENDIR):
	@mkdir -p $@

$(GENDIR)/index.md: $(SOURCES) generate.py | $(GENDIR)
	@rm -rf $(GENDIR)/*
	@python3 generate.py --template "$(SOURCEDIR)" --root "$(ROOTDIR)/html" --output "$(GENDIR)"

# Build the final webpage. Pass the 'html' target to sphinx, copy report pages
html: Makefile $(GENDIR)/index.md
	@$(SPHINXBUILD) -M $@ "$(GENDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
	@rsync -avrm --include="*/" --include="coverage_dashboard/***" --include="verification_dashboard/***" --exclude="*" "$(ROOTDIR)/" "$(BUILDDIR)/"
	@bash update_styles.sh "$(BUILDDIR)"

clean:
	@rm -rf $(BUILDDIR)
	@rm -rf $(GENDIR)

.PHONY: all clean html
