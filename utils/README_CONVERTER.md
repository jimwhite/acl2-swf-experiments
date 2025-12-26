# Lisp to Jupyter Notebook Converter

Scripts to convert ACL2/Common Lisp `.lisp` files into Jupyter `.ipynb` notebooks.

## Usage

### Using Make (Recommended)

The easiest way to keep notebooks up-to-date is using the Makefile in the project root:

```bash
# Convert all out-of-date notebooks
make

# Certify all out-of-date ACL2 books
make certify

# Check which notebooks need updating
make check

# Check which books need certification
make check-cert

# Show status of all notebooks
make list

# Build a specific notebook
make experiments/lists/experiment-02-higher-order.ipynb

# Certify a specific book
make experiments/lists/experiment-02-higher-order.cert

# See all available targets
make help
```

The Makefile automatically:
- Only rebuilds notebooks when the `.lisp` file is newer than the `.ipynb` file
- Only recertifies books when the `.lisp` file is newer than the `.cert` file
- Tracks dependencies on the converter script and included books
- Skips files in `.ipynb_checkpoints/` directories

### Direct SBCL Script Usage (Recommended)

The SBCL-based converter uses the Common Lisp reader to properly parse source files,
correctly identifying standalone comment blocks vs. code with associated comments.

```bash
# Convert an ACL2 file
./utils/lisp-to-ipynb --acl2 input.lisp [output.ipynb]

# Convert a Common Lisp file (default)
./utils/lisp-to-ipynb input.lisp [output.ipynb]
```

Cell boundary rules:
- Blank lines separate cells (groups of content)
- A group that contains ONLY comments becomes a markdown cell
- A group that contains ANY code becomes a code cell (comments included)

Examples:
```bash
# ACL2 mode - sets kernel to ACL2 and language to acl2
./utils/lisp-to-ipynb --acl2 experiments/agents/experiment-01-react-verified.lisp

# Common Lisp mode (default) - sets kernel to Common Lisp
./utils/lisp-to-ipynb utils/lisp-to-ipynb.lisp
```

### Legacy Python Script Usage

For simpler files, the Python script can also be used:

#### Convert a single file

```bash
python3 utils/lisp_to_ipynb.py <input.lisp> [output.ipynb]
```

Examples:
```bash
# Convert to default output name (same as input but .ipynb)
python3 utils/lisp_to_ipynb.py experiments/lists/experiment-02-higher-order.lisp

# Specify custom output name
python3 utils/lisp_to_ipynb.py input.lisp custom-output.ipynb
```

#### Convert multiple files

```bash
python3 utils/lisp_to_ipynb.py file1.lisp file2.lisp file3.lisp
```

## Conversion Rules

1. **Cell grouping**: Consecutive non-blank lines are grouped into a single cell
2. **Blank lines**: Act as cell separators
3. **Comment-only blocks**: If all non-blank lines in a group start with `;`, the cell is marked as `raw` (for documentation)
4. **Code blocks**: Any group containing at least one non-comment line is marked as `acl2` code
5. **Language**: All code cells use the `acl2` language identifier

## Example

Input `.lisp` file:
```lisp
; This is a comment block
; It will become a raw cell

(in-package "ACL2")

; This function has a comment but also code
(defun my-func (x)
  (+ x 1))
```

Output `.ipynb` structure:
- Cell 1 (raw): The comment block
- Cell 2 (acl2): `(in-package "ACL2")`
- Cell 3 (acl2): The function definition with its comment

## Requirements

- Python 3.6+
- Standard library only (no external dependencies)

## Files

- `lisp_to_ipynb.py` - Main conversion script
- `convert_all_lisp.sh` - Batch conversion helper script
- `README_CONVERTER.md` - This file
