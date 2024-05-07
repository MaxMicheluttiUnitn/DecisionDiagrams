# Decision Diagrams and dDNNFs

## Running

This is the implementation of the code for my project course with professor R. Sebastiani of the University of Trento and doctorands G. Spallitta and G. Masina. 
To try out the code just type in the project folder:

```
    python3 main.py
```

## Installation

First install the dd package with cython and wheel. This is a fork of the official dd package that can be installed directly from pip, which adds bindings for generating LDDs. You can find more info at [this link](https://github.com/masinag/dd).

```
    pip install --upgrade wheel cython
    export DD_FETCH=1 DD_CUDD=1 DD_LDD=1
    pip install git+https://github.com/masinag/dd.git@main -vvv --use-pep517 --no-build-isolation
```

To check that this step completed successfully, the following command should not yield any errors

```
    python -c 'from dd import ldd; ldd.LDD(ldd.TVPI,0,0)'
```

Then install all other dependencies of the project

```
    pip install -r requirements.txt
```

Finally install the Mathsat SMT-solver from the pysmt package

```
    pysmt-install --msat
```

## Compiking to dDNNF

The tool supports both abstraction based and theory consistent compilation in dDNNF. However, in order to compile to this language you will need to download the dDNNF compiler [c2d](http://reasoning.cs.ucla.edu/c2d/). Download it and put the binary inside the tool main folder. Remember to grant the binary permission to execute.

```
    chmod +x c2d_linux
```

Compilation in dDNNF is currently not supported by the tool for other operative systems.


## Dumping XSDDs

When using XSDDs be careful to install https://github.com/ML-KULeuven/psipy instead of the default psipy to use the PSI solver

The dd library was slightly changed to allow for .dot dumping as follows:

```
def dump(self, filename, roots=None,
             filetype=None, **kw):
        if filetype is None:
            name = filename.lower()
            if name.endswith('.pdf'):
                filetype = 'pdf'
            elif name.endswith('.png'):
                filetype = 'png'
            elif name.endswith('.svg'):
                filetype = 'svg'
            elif name.endswith('.p'):
                filetype = 'pickle'
            elif name.endswith('.dot'):
                filetype = 'dot'
            else:
                raise Exception((
                    'cannot infer file type '
                    'from extension of file '
                    'name "{f}"').format(
                        f=filename))
        if filetype in ('pdf', 'png', 'svg', 'dot'):
            self._dump_figure(roots, filename,
                              filetype, **kw)
        elif filetype == 'pickle':
            self._dump_bdd(roots, filename, **kw)
        else:
            raise Exception(
                'unknown file type "{t}"'.format(
                    t=filetype))

    def _dump_figure(self, roots, filename,
                     filetype, **kw):
        """Write BDDs to `filename` as figure."""
        g = to_pydot(roots, self)
        if filetype == 'pdf':
            g.write_pdf(filename, **kw)
        elif filetype == 'png':
            g.write_png(filename, **kw)
        elif filetype == 'svg':
            g.write_svg(filename, **kw)
        elif filetype == 'dot':
            g.write(filename, **kw)
        else:
            raise Exception(
                'Unknown file type of "{f}"'.format(
                    f=filename))
```