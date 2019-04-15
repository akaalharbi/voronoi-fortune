# Frequent minor updates

##  Thursday, 14. March 2019 02:18 
* Setting up a GitHub account
* Learning basic git workflow
* Organizing files 

## Friday, 15. March 2019 06:02 
 I started reading the implementation mentioned in [here](http://blog.ivank.net/fortunes-algorithm-and-implementation.html). However, there are some cases there are not covered in the implementation. For instance, when a new site is introduced and the perpendicular line intersects two arcs (i.e. break points) is not mentioned. It seems the distance function is always assumed to be the Euclidean one, it's not clear what will break if it was another distance function ( Probably, it will make ordering points more difficult) .

## Friday, 29. March 2019 05:47 
	
 *  Implementing the algorithm in python took more than what I expected. Few factors contributed to this. 
	* Trying to implement it directly in without writing a high-level draft which led to inconsistency in integrating between the components.
	* Lack of visualization of the code's output made debugging rather painful.
	* Shallow understanding of the algorithm. 
		
## Friday, 12 April 2019. 18:28 
I was able to translate the python code to coq. It was, mostly, a straightforward process. There might be some typos, especially in the handling functions. I have ignored the following:

* Adding a bounding box at the end.
* When a site event occurs, it might create one edge instead of two.


### Statistics

**Unit: number of lines**

lang|Duration|insertions| avg | Deletions | avg | total | avg 
----|--------|----------|-----|-----------|-----|-------|-----
`python`| 12 days | 1741 | 145.1 | 1113 | 92 .75 | 628 | 52.3 
`coq` | 7 days | 1004 | 143.43 | 495 | 70.71 | 509 | 72.71



If we assume that the proof is 10 times larger than the program, and the proofs writing speed lies between 52.3-72.71 *lines/day*, then one expects this to be done in sometime between 70 working days and 120 working days. In reality, it might take longer as I did not need to search about python syntax while implementing the algorithm.