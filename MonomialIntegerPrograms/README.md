## Monomial Integer Programs package for Macaulay2

### A package for fast monomial ideal computations using constraint integer programming

   This package uses integer program reformulations to perform faster
   computations on monomial ideals. The functions currently available
   are:
   
  * **codimensionIP**: codimension of a monomial ideal
   
  * **dimensionIP**: dimension of a monomial ideal
   
  * **degreeIP**: degree of a monomial ideal, currently for squarefree only
   
  * **topMinimalPrimesIP**: lists all minimal primes of maximum dimension
   
  * **monomialIdealsWithHilbertFunction**: lists all monomial ideals in a given ring
   with a given Hilbert function
   
   Additional functions are in development.
  
  
  ### Installation and licensing information.
   
   This package relies on the constraint integer program solver SCIP, which
   is available at https://scip.zib.de/. This software is free for
   for academic, non-commercial purposes. Notice that SCIP is not distributed 
   under GPL, but under the ZIB Academic License (https://scip.zib.de/academic.txt).
  
   To install SCIP, click the *Download* tab on the left-hand side of the
   SCIP home page. The easiest method is to install prebuilt binaries (look for the heading
   *Installers (install the scipoptsuite in your computer, without source files)*.
   Choose the appropriate Linux, Windows, or MacOS file. The download is free,
   but you will be asked to submit your name and academic institution, to conform to
   the ZIB Academic License requirements, before the download begins.
  
   Under the heading *Source Code*, you can find the files for building
   from source. If building from source, you MUST include the source files for
   the modeling language Zimpl in order to use the Monomial Integer 
   Programs package. This will be included if you choose the download named 
   SCIP Optimization Suite, rather than the one named SCIP. Alternatively, download
   SCIP and then follow the *ZIMPL* link at the top of the home page to
   download the source files for Zimpl. When building SCIP, you will have to set
   a flag indicating that Zimpl should be built as well. For more information about
   building SCIP visit their online documentation (https://scip.zib.de/doc-6.0.0/html/)
   and click on *Overview -> Getting started ->
   Installing SCIP*.
  
   An excellent user guide to using Zimpl can be found at 
   https://zimpl.zib.de/download/zimpl.pdf. The author, Thorsten
   Koch, requests that research making use of this software please
   cite his 2004 PhD thesis, *Rapid Mathematical Programming*. The
   appropriate BibTeX entry can be found here: https://zimpl.zib.de/download/zimpl.bib.
   Zimpl is distributed under GPL.
  
   Additionally, any research that uses SCIP needs a proper citation. See the
   *How to Cite* tab on their home page.  
     
