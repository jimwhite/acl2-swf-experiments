# Makefile for converting ACL2 .lisp files to Jupyter .ipynb notebooks
# and certifying ACL2 books
# Only rebuilds/recertifies when source files are newer

# Path to the converter script
CONVERTER_SCRIPT := utils/lisp-to-ipynb.lisp
CONVERTER := sbcl --script $(CONVERTER_SCRIPT) --acl2

# Path to ACL2 certification tool
CERT := cert.pl

# Find all .lisp files in experiments directory (excluding .ipynb_checkpoints)
# Use DIR variable to limit scope: make certify DIR=experiments/agents
# Use SKIP variable to exclude files: make certify SKIP="file1.lisp file2.lisp"
DIR ?= experiments

SKIP ?= experiments/agents/react-agent-v4.lisp \
	experiments/agents/mcp-client-old.lisp \
	experiments/agents/test-mcp-session.lisp \
	experiments/agents/test-llm.lisp \
	experiments/challenge-problems-old.lisp

LISP_FILES_ALL := $(shell find $(DIR) -name "*.lisp" -type f ! -path "*/.ipynb_checkpoints/*")
LISP_FILES := $(filter-out $(SKIP),$(LISP_FILES_ALL))

# Generate corresponding .ipynb targets
NOTEBOOKS := $(LISP_FILES:.lisp=.ipynb)

# Generate corresponding .cert targets
CERTS := $(LISP_FILES:.lisp=.cert)

# Pattern rule: how to build a .ipynb from a .lisp
%.ipynb: %.lisp $(CONVERTER_SCRIPT)
	@echo "Converting $< -> $@"
	$(CONVERTER) $<

# Default target: build all notebooks
.PHONY: all
all: $(NOTEBOOKS)

# Certify all ACL2 books
.PHONY: certify
certify: $(CERTS)

# Pattern rule: how to certify a .lisp book
%.cert: %.lisp
	@echo "Certifying $<..."
	@cd $(dir $<) && $(CERT) $(notdir $<)

# Clean target: remove all generated notebooks
.PHONY: clean-notebooks
clean-notebooks:
	@echo "Removing all generated .ipynb files..."
	@rm -f $(NOTEBOOKS)
	@echo "Done!"

# Clean certificates: remove all .cert files and related ACL2 output
.PHONY: clean
clean:
	@echo "Removing all .cert files and ACL2 output..."
	@find experiments -type f \( -name "*.cert" -o -name "*.out" -o -name "*.time" -o -name "*.port" -o -name "*.fasl" \) -delete
	@echo "Done!"

# Clean everything: notebooks and certificates
.PHONY: clean-all
clean-all: clean clean-notebooks

# List target: show all .lisp files and their notebook status
.PHONY: list
list:
	@echo "Lisp source files and their notebooks:"
	@for lisp in $(LISP_FILES); do \
		ipynb=$${lisp%.lisp}.ipynb; \
		if [ -f $$ipynb ]; then \
			if [ $$lisp -nt $$ipynb ]; then \
				echo "  [OUT-OF-DATE] $$lisp -> $$ipynb"; \
			else \
				echo "  [UP-TO-DATE]  $$lisp -> $$ipynb"; \
			fi; \
		else \
			echo "  [MISSING]     $$lisp -> $$ipynb"; \
		fi; \
	done

# Check target: list only out-of-date or missing notebooks
.PHONY: check
check:
	@echo "Out-of-date or missing notebooks:"
	@found=0; \
	for lisp in $(LISP_FILES); do \
		ipynb=$${lisp%.lisp}.ipynb; \
		if [ ! -f $$ipynb ]; then \
			echo "  [MISSING]     $$lisp"; \
			found=1; \
		elif [ $$lisp -nt $$ipynb ]; then \
			echo "  [OUT-OF-DATE] $$lisp"; \
			found=1; \
		fi; \
	done; \
	if [ $$found -eq 0 ]; then \
		echo "  All notebooks are up-to-date!"; \
	fi

# Check certifications: list only out-of-date or missing .cert files
.PHONY: check-cert
check-cert:
	@echo "Out-of-date or missing certifications:"
	@found=0; \
	for lisp in $(LISP_FILES); do \
		cert=$${lisp%.lisp}.cert; \
		if [ ! -f $$cert ]; then \
			echo "  [MISSING]     $$lisp"; \
			found=1; \
		elif [ $$lisp -nt $$cert ]; then \
			echo "  [OUT-OF-DATE] $$lisp"; \
			found=1; \
		fi; \
	done; \
	if [ $$found -eq 0 ]; then \
		echo "  All books are certified!"; \
	fi

.PHONY: acl2-mcp
acl2-mcp:
	pip install git+https://github.com/septract/acl2-mcp.git
	@echo "Use 'acl2-mcp' to run ACL2 MCP service."

# Help target
.PHONY: help
help:
	@echo "Makefile for ACL2 .lisp to .ipynb conversion and book certification"
	@echo ""
	@echo "Notebook Targets:"
	@echo "  make all        - Convert all updated .lisp files to .ipynb (default)"
	@echo "  make clean      - Remove all generated .ipynb files"
	@echo "  make check      - Show only out-of-date or missing notebooks"
	@echo "  make list       - Show all .lisp files and their notebook status"
	@echo ""
	@echo "Certification Targets:"
	@echo "  make certify    - Certify all out-of-date ACL2 books (.cert files)"
	@echo "  make clean-cert - Remove all .cert and ACL2 output files"
	@echo "  make check-cert - Show only out-of-date or missing certifications"
	@echo ""
	@echo "Combined Targets:"
	@echo "  make clean-all  - Remove all generated files (notebooks + certs)"
	@echo "  make help       - Show this help message"
	@echo ""
	@echo "Limiting scope with DIR:"
	@echo "  make certify DIR=experiments/agents     # Only certify agents/"
	@echo "  make check-cert DIR=experiments/lists   # Check lists/ books"
	@echo ""
	@echo "Examples:"
	@echo "  make                              # Build all out-of-date notebooks"
	@echo "  make certify                      # Certify all out-of-date books"
	@echo "  make experiments/lists/experiment-01-list-basics.ipynb"
	@echo "                                    # Build a specific notebook"
	@echo "  make experiments/lists/experiment-01-list-basics.cert"
	@echo "                                    # Certify a specific book"
	@echo "  make check                        # Check which notebooks need updating"
	@echo "  make check-cert                   # Check which books need certification"
	@echo ""
	@echo "The Makefile only rebuilds/recertifies when:"
	@echo "  - The target file doesn't exist, OR"
	@echo "  - The .lisp source file is newer than the target"
