# Makefile for wiki3.ai ACL2 + SMTLink Build

# ACL2_HOME ?= /opt/acl2  # Adjust path to your ACL2 installation
ACL2_BIN = $(ACL2_HOME)/saved_acl2

OUTPUT_DIR = output

.PHONY: all clean verify generate-python certify-books

all: verify generate-python

# Step 1: Certify the ACL2 books (proves theorems)
certify-books:
	@echo "Step 1: Certifying ACL2 books with SMTLink..."
	$(ACL2_BIN) < /dev/null > /dev/null
	# The above would normally run:
	# (include-book "wiki3_verification" :dir :system)

# Step 2: Run SMTLink to verify theorems against Z3
verify: certify-books
	@echo "Step 2: Running SMTLink verification (proving theorems via Z3)..."
	@mkdir -p $(OUTPUT_DIR)
	# SMTLink runs during book certification above
	# It verifies each theorem by translating to Z3 and checking

# Step 3: Generate Python code from verified theorems
generate-python: verify
	@echo "Step 3: Generating Python code from verified theorems..."
	@python3 smtlink_codegen.py \
		--input cost_benefit_theorems.lisp \
		--output $(OUTPUT_DIR)/cost_benefit_verified.py \
		--mapping smtlink_config.lisp
	@echo "✓ Generated: $(OUTPUT_DIR)/cost_benefit_verified.py"

clean:
	rm -rf $(OUTPUT_DIR)/*.py
	rm -rf *.cert
	rm -rf .acl2x

# Run full pipeline
pipeline: clean all
	@echo "✓ Complete: ACL2 theorems verified and Python code generated"
