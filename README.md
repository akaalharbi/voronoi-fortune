# Voronoi-Fortune
Fortune's algorithm described in coq

## Overview 
Fortune's algorithm is a sweep line algorithm to construct the Voronoi diagram of a set of points in the plane. *In this task*, we wish to develop  **a formal description of Voronoi diagrams and of the algorithm proposed by Steven Fortune in 1986,** in the context of the [Coq](https://coq.inria.fr/) system and the [mathematical components library](http://math-comp.github.io/math-comp/). If time allows, we also wish to study how executable algorithms can be derived from the formal description.

## Files
* [`doc/`](doc/) 
	* [`progress `](doc/progress.md)  contains an overview of the small progress achieved over  short periods.
	* [`resources`](doc/resources.md) a bibliography  for learning [Coq](https://coq.inria.fr/) and Fortune's algorithm.
	*  [`plan`](doc/plan.md) high levle goals and their deadlines 
	* [`proofs outlines`](doc/proofs-outlines.tex)  a sketch  of a proof the correctness of the algorithm.
	* [`polynomial-equalities-experiment`](doc/polynomial-equalities-experiment.v) A basic demo of how to prove identities in a [ring](https://en.wikipedia.org/wiki/Ring_(mathematics)) using the [mathematical components](http://math-comp.github.io/math-comp/) library.
* [`python/`](python/) a python implementation of Fotune's algorithm.
	