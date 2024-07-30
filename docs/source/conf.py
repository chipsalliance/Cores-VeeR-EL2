from datetime import datetime

from antmicro_sphinx_utils.defaults import (
    extensions as default_extensions,
    myst_enable_extensions as default_myst_enable_extensions,
    myst_fence_as_directive as default_myst_fence_as_directive,
    antmicro_html,
)

# General information about the project.
project = u'RISC-V VeeR EL2 Programmer\'s Reference Manual'
basic_filename = u'riscv-veer-el2-prm'
authors = u'CHIPS Alliance The Linux Foundation®'
copyright = f'{datetime.now().year} {authors}'

# The short X.Y version.
version = ''
# The full version, including alpha/beta/rc tags.
release = ''

# This is temporary before the clash between myst-parser and immaterial is
# fixed
sphinx_immaterial_override_builtin_admonitions = False

numfig = True

# If you need to add extensions just add to those lists
extensions = default_extensions
myst_enable_extensions = default_myst_enable_extensions
myst_fence_as_directive = default_myst_fence_as_directive

myst_substitutions = {
    "project": project
}

myst_heading_anchors = 4

today_fmt = '%Y-%m-%d'

todo_include_todos=False

# -- Options for HTML output ---------------------------------------------------

html_theme = 'sphinx_immaterial'

html_last_updated_fmt = today_fmt

html_show_sphinx = False

(
    html_logo,
    html_theme_options,
    html_context
) = antmicro_html()

html_theme_options["palette"][0].update({
    "scheme": "slate",
    "primary": "teal",
    "accent": "white",
})

def setup(app):
    app.add_css_file('main.css')
