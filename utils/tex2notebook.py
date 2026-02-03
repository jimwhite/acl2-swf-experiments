#!/usr/bin/env python3
"""
Convert a LaTeX paper with ACL2 code examples to a Jupyter notebook.

This script:
1. Reads the main .tex file and resolves \input{} includes
2. Uses pandoc to convert LaTeX to markdown
3. Parses the result to separate prose from code blocks
4. Creates a Jupyter notebook with markdown and ACL2 code cells

Requirements:
    pip install nbformat pypandoc
    # Also needs pandoc installed: apt-get install pandoc
"""

import re
import os
import sys
import argparse
from pathlib import Path

import nbformat
from nbformat.v4 import new_notebook, new_markdown_cell, new_code_cell

try:
    import pypandoc
except ImportError:
    print("Installing pypandoc...")
    import subprocess
    subprocess.check_call([sys.executable, "-m", "pip", "install", "pypandoc"])
    import pypandoc


def resolve_inputs(tex_content: str, base_dir: Path) -> str:
    """Recursively resolve \input{file} and \include{file} commands."""
    
    def replace_input(match):
        filename = match.group(1)
        # Add .tex extension if not present
        if not filename.endswith('.tex'):
            filename += '.tex'
        
        filepath = base_dir / filename
        if filepath.exists():
            print(f"  Including: {filename}")
            included_content = filepath.read_text()
            # Recursively resolve inputs in the included file
            return resolve_inputs(included_content, base_dir)
        else:
            print(f"  Warning: Could not find {filepath}")
            return f"% Could not include: {filename}"
    
    # Match \input{file} or \include{file}
    pattern = r'\\(?:input|include)\{([^}]+)\}'
    return re.sub(pattern, replace_input, tex_content)


def preprocess_latex(tex_content: str) -> str:
    """Preprocess LaTeX to help pandoc and preserve code blocks."""
    
    # Remove document class and preamble up to \begin{document}
    # but keep the content after \begin{document}
    doc_match = re.search(r'\\begin\{document\}(.*)\\end\{document\}', 
                          tex_content, re.DOTALL)
    if doc_match:
        tex_content = doc_match.group(1)
    
    # Remove \maketitle
    tex_content = re.sub(r'\\maketitle', '', tex_content)
    
    # Convert \verb|...| to inline code (before pandoc mangles it)
    tex_content = re.sub(r'\\verb\|([^|]*)\|', r'`\1`', tex_content)
    tex_content = re.sub(r'\\verb\+([^+]*)\+', r'`\1`', tex_content)
    
    # Mark verbatim blocks with special markers so we can find them later
    # Pandoc converts them but we want to make them ACL2 code cells
    verbatim_blocks = []
    
    def save_verbatim(match):
        code = match.group(1)
        idx = len(verbatim_blocks)
        verbatim_blocks.append(code)
        # Use a unique marker that won't be altered by pandoc
        return f'\n\n<!--CODEBLOCK_{idx}-->\n\n'
    
    # Handle both verbatim and Verbatim (from fancyvrb)
    tex_content = re.sub(
        r'\\begin\{[Vv]erbatim\}(?:\[[^\]]*\])?\s*\n?(.*?)\n?\\end\{[Vv]erbatim\}',
        save_verbatim,
        tex_content,
        flags=re.DOTALL
    )
    
    # Also handle lstlisting environments
    tex_content = re.sub(
        r'\\begin\{lstlisting\}(?:\[[^\]]*\])?\s*\n?(.*?)\n?\\end\{lstlisting\}',
        save_verbatim,
        tex_content,
        flags=re.DOTALL
    )
    
    # Remove bibliography commands (pandoc doesn't handle them well)
    tex_content = re.sub(r'\\bibliographystyle\{[^}]*\}', '', tex_content)
    tex_content = re.sub(r'\\bibliography\{[^}]*\}', '', tex_content)
    
    # Remove acknowledgments section for cleaner output
    tex_content = re.sub(r'\\section\*?\{Acknowledgments?\}.*?(?=\\section|$)', 
                         '', tex_content, flags=re.DOTALL | re.IGNORECASE)
    
    # Clean up hyperlinks - convert to markdown style
    # \href{url}{\underline{text}} -> [text](url)
    tex_content = re.sub(
        r'\\href\{([^}]*)\}\{\\underline\{([^}]*)\}\}',
        r'[\2](\1)',
        tex_content
    )
    tex_content = re.sub(
        r'\\href\{([^}]*)\}\{([^}]*)\}',
        r'[\2](\1)',
        tex_content
    )
    
    # Remove remaining underlines
    tex_content = re.sub(r'\\underline\{([^}]*)\}', r'\1', tex_content)
    
    # Convert \texttt{} to backticks
    tex_content = re.sub(r'\\texttt\{([^}]*)\}', r'`\1`', tex_content)
    tex_content = re.sub(r'\{\\tt\s+([^}]*)\}', r'`\1`', tex_content)
    
    # Handle \becomes macro
    tex_content = re.sub(r'\\becomes', "'becomes'", tex_content)
    
    # Remove \noindent
    tex_content = re.sub(r'\\noindent\s*', '', tex_content)
    
    # Handle footnotes - convert to inline notes
    tex_content = re.sub(r'\\footnote\{([^}]*)\}', r' (*Note: \1*)', tex_content)
    
    return tex_content, verbatim_blocks


def latex_to_markdown(tex_content: str) -> str:
    """Convert LaTeX to Markdown using pandoc."""
    try:
        markdown = pypandoc.convert_text(
            tex_content,
            'markdown',
            format='latex',
            extra_args=['--wrap=none']  # Don't wrap lines
        )
        return markdown
    except Exception as e:
        print(f"Pandoc conversion error: {e}")
        print("Falling back to basic conversion...")
        return basic_latex_to_markdown(tex_content)


def basic_latex_to_markdown(tex_content: str) -> str:
    """Basic LaTeX to Markdown conversion as fallback."""
    content = tex_content
    
    # Sections
    content = re.sub(r'\\section\*?\{([^}]*)\}', r'# \1', content)
    content = re.sub(r'\\subsection\*?\{([^}]*)\}', r'## \1', content)
    content = re.sub(r'\\subsubsection\*?\{([^}]*)\}', r'### \1', content)
    
    # Emphasis
    content = re.sub(r'\\emph\{([^}]*)\}', r'*\1*', content)
    content = re.sub(r'\\textbf\{([^}]*)\}', r'**\1**', content)
    content = re.sub(r'\{\\em\s+([^}]*)\}', r'*\1*', content)
    content = re.sub(r'\{\\bf\s+([^}]*)\}', r'**\1**', content)
    
    # Lists
    content = re.sub(r'\\begin\{itemize\}', '', content)
    content = re.sub(r'\\end\{itemize\}', '', content)
    content = re.sub(r'\\begin\{enumerate\}', '', content)
    content = re.sub(r'\\end\{enumerate\}', '', content)
    content = re.sub(r'\\item\s*', '\n- ', content)
    
    # Math
    content = re.sub(r'\$([^$]+)\$', r'$\1$', content)
    
    # Labels and refs (remove them)
    content = re.sub(r'\\label\{[^}]*\}', '', content)
    content = re.sub(r'\\ref\{[^}]*\}', '[ref]', content)
    content = re.sub(r'~', ' ', content)  # Non-breaking space
    
    # Citations
    content = re.sub(r'\\cite\{[^}]*\}', '[citation]', content)
    
    # Remove remaining LaTeX commands
    content = re.sub(r'\\[a-zA-Z]+\*?(?:\[[^\]]*\])?\{([^}]*)\}', r'\1', content)
    content = re.sub(r'\\[a-zA-Z]+\*?', '', content)
    
    return content


def is_acl2_code(code: str) -> bool:
    """Heuristically determine if code block is ACL2/Lisp code."""
    # Check for common ACL2/Lisp patterns
    acl2_patterns = [
        r'\(defun\b', r'\(defthm\b', r'\(defconst\b',
        r'\(include-book\b', r'\(in-package\b',
        r'\(if\b', r'\(let\b', r'\(cond\b',
        r'\(declare\b', r'\(xargs\b',
        r'\(equal\b', r'\(implies\b',
        r'ACL2\s*!>', r':pf\b', r':pe\b',
        r'\(simplify-defun\b', r'\(mutual-recursion\b',
        r'\(defstub\b', r'\(encapsulate\b',
        r'\(zp\b', r'\(natp\b', r'\(consp\b',
    ]
    
    code_lower = code.lower()
    for pattern in acl2_patterns:
        if re.search(pattern, code, re.IGNORECASE):
            return True
    
    # Check if it looks like Java/C code instead
    non_acl2_patterns = [
        r'\bstatic\s+void\b', r'\bint\s+\w+\s*=',
        r'\bwhile\s*\(', r'\bif\s*\([^)]+\)\s*\{',
        r'\breturn\b.*;', r'\b\w+\+\+',
    ]
    for pattern in non_acl2_patterns:
        if re.search(pattern, code):
            return False
    
    # Default to ACL2 if it has lots of parentheses
    paren_ratio = code.count('(') / max(len(code), 1)
    return paren_ratio > 0.05


def split_into_cells(markdown: str, code_blocks: list) -> list:
    """Split markdown into notebook cells, restoring code blocks."""
    cells = []
    
    # Split by code block markers
    parts = re.split(r'<!--CODEBLOCK_(\d+)-->', markdown)
    
    i = 0
    while i < len(parts):
        text = parts[i].strip()
        
        if text:
            # Clean up excessive newlines
            text = re.sub(r'\n{3,}', '\n\n', text)
            # Split very long markdown sections at section headers
            sections = re.split(r'(?=^#+ )', text, flags=re.MULTILINE)
            for section in sections:
                section = section.strip()
                if section:
                    cells.append(('markdown', section))
        
        i += 1
        
        # Check if next part is a code block index
        if i < len(parts):
            try:
                code_idx = int(parts[i])
                if code_idx < len(code_blocks):
                    code = code_blocks[code_idx].strip()
                    if code:
                        cell_type = 'code' if is_acl2_code(code) else 'markdown'
                        if cell_type == 'markdown':
                            # Wrap non-ACL2 code in markdown code block
                            code = f"```\n{code}\n```"
                        cells.append((cell_type, code))
                i += 1
            except ValueError:
                pass
    
    return cells


def create_notebook(cells: list, title: str = "Simplifying Definitions with simplify-defun") -> nbformat.NotebookNode:
    """Create a Jupyter notebook from cells."""
    nb = new_notebook()
    
    # Set notebook metadata for ACL2 kernel (if available) or default to common-lisp
    nb.metadata['kernelspec'] = {
        'display_name': 'Common Lisp',
        'language': 'common-lisp', 
        'name': 'common-lisp'
    }
    nb.metadata['language_info'] = {
        'name': 'common-lisp',
        'version': '',
        'mimetype': 'text/x-common-lisp',
        'file_extension': '.lisp'
    }
    
    # Add title cell
    title_cell = new_markdown_cell(f"# {title}\n\n*Adapted from: A Versatile, Sound Tool for Simplifying Definitions*\n\n*Authors: Alessandro Coglio, Matt Kaufmann, Eric W. Smith*\n\n*ACL2 Workshop 2017*")
    nb.cells.append(title_cell)
    
    # Add the rest of the cells
    for cell_type, content in cells:
        if cell_type == 'markdown':
            nb.cells.append(new_markdown_cell(content))
        else:
            nb.cells.append(new_code_cell(content))
    
    return nb


def convert_paper(input_path: str, output_path: str):
    """Main conversion function."""
    input_path = Path(input_path)
    output_path = Path(output_path)
    base_dir = input_path.parent
    
    print(f"Reading {input_path}...")
    tex_content = input_path.read_text()
    
    print("Resolving includes...")
    tex_content = resolve_inputs(tex_content, base_dir)
    
    print("Preprocessing LaTeX...")
    tex_content, code_blocks = preprocess_latex(tex_content)
    print(f"  Found {len(code_blocks)} code blocks")
    
    print("Converting to Markdown with pandoc...")
    markdown = latex_to_markdown(tex_content)
    
    print("Splitting into cells...")
    cells = split_into_cells(markdown, code_blocks)
    print(f"  Created {len(cells)} cells")
    
    print("Creating notebook...")
    nb = create_notebook(cells)
    
    print(f"Writing to {output_path}...")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w') as f:
        nbformat.write(nb, f)
    
    print(f"Done! Created notebook with {len(nb.cells)} cells.")
    return nb


def main():
    parser = argparse.ArgumentParser(
        description='Convert LaTeX paper with ACL2 code to Jupyter notebook'
    )
    parser.add_argument(
        'input', 
        nargs='?',
        default='paper.tex',
        help='Input LaTeX file (default: paper.tex)'
    )
    parser.add_argument(
        'output',
        nargs='?', 
        default=None,
        help='Output notebook file (default: derived from input)'
    )
    parser.add_argument(
        '-o', '--output-dir',
        default=None,
        help='Output directory for the notebook'
    )
    
    args = parser.parse_args()
    
    input_path = Path(args.input)
    if not input_path.exists():
        print(f"Error: Input file {input_path} not found")
        sys.exit(1)
    
    if args.output:
        output_path = Path(args.output)
    else:
        output_name = input_path.stem + '.ipynb'
        if args.output_dir:
            output_path = Path(args.output_dir) / output_name
        else:
            output_path = input_path.parent / output_name
    
    convert_paper(input_path, output_path)


if __name__ == '__main__':
    main()
