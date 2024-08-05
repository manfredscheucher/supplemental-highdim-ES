# A SAT attack on higher dimensional Erdös--Szekeres numbers

This website provides programs to verify the computer-assisted results from my paper "A SAT attack on higher dimensional Erdös--Szekeres numbers".

## Abstract of the paper

A famous result by Erdös and Szekeres (1935) asserts that, for all $k,d \in \mathbb{N}$, there is a smallest integer $n = g^{(d)}(k)$, such that every set of at least $n$ points in $\mathbb{R}^d$ in general position contains a \emph{$k$-gon}, that is, a subset of $k$ points which is in convex position. In this article, we present a SAT model based on acyclic chirotopes (oriented matroids) to investigate Erdös--Szekeres numbers in small dimensions. To solve the SAT instances use modern SAT solvers and all our unsatisfiability results are verified using DRAT certificates. We show $g^{(3)}(7) = 13$, $g^{(4)}(8) \le 13$, and $g^{(5)}(9) \le 13$, which are the first improvements for decades. For the setting of \emph{$k$-holes} (i.e., $k$-gons with no other points in the convex hull), where $h^{(d)}(k)$ denotes the minimum number $n$ such that every set of at least $n$ points in $\mathbb{R}^d$ in general position contains a $k$-hole, we show $h^{(3)}(7) \le 14$, $h^{(4)}(8) \le 13$, and $h^{(5)}(9) \le 13$. Moreover, all obtained bounds are sharp in the setting of acyclic chirotopes and we conjecture them to be sharp also in the original setting of point sets. As a byproduct, we verify all previous known bounds and, in particular, present the first computer-assisted proof of the upper bound $h^{(2)}(6)\le g^{(2)}(9) \le 1717$ by Gerken (2008).

## Description of the programs

We provide a python program "test_ES.py" to formulate a SAT instance to verify our obtained bounds on $g^{(d)}(k)$ and $h^{(d)}(k)$ for dimensions $d=3,4,5$.

*   To create an instance for verifying $g^{(3)}(7) \le 13$, run
    
    ```python test_ES.py 0 7 3 13```
    
*   To create an instance for verifying $h^{(3)}(7) \le 14$, run
    
    ```python test_ES.py 1 7 3 14```
    
*   To create an instance for verifying $h^{(4)}(8) \le 13$, run
    
    ```python test_ES.py 1 8 4 13```
    
*   To create an instance for verifying $h^{(5)}(9) \le 13$, run
    
    ```python test_ES.py 1 9 5 13```
    

The program can also be used to verify previously known bounds on $g^{(d)}(k)$ and $h^{(d)}(k)$ in dimensions $d=2,3$.

*   To create an instance for verifying $g^{(2)}(5) \le 9$ (Makai 1935), run
    
    ```python test_ES.py 0 5 2 9```
    
*   To create an instance for verifying $g^{(2)}(6) \le 17$ (Szekeres and Peters 2006), run
    
    ```python test_ES.py 0 6 2 17```
    
*   To create an instance for verifying $h^{(2)}(5) \le 10$ (Harborth 1978), run
    
    ```python test_ES.py 1 5 2 10```
    
*   To create an instance for verifying $h^{(3)}(6) \le 9$ (Bisztriczky and Soltan 1994), run
    
    ```python test_ES.py 1 6 3 9```
    

The first parameter "0" indicates that we forbid $k$-gons and "1" indicates that we forbid $k$-holes. The value $k$ is specified in the second parameter. The third parameter specifies the dimension $d$. The fourth parameter specifies the number of points $n$. The SAT instance is written to a CNF-file, which then can be solved using a SAT solver such as [CaDiCaL](http://fmv.jku.at/cadical/):

```cadical [instance]```

In case of unsatisfiability, CaDiCal can create a unsatisfiability proof, which can then be verified by a proof checking tool such as [DRAT-trim](https://www.cs.utexas.edu/~marijn/drat-trim/):

```cadical [instance] [proof] && drat-trim [instance] [proof]```

### Existence of planar 6-holes

We have slightly adapted the general program "test_ES.py" to verify the bound $h^{(2)}(6) \le g^{(2)}(9)$ (Gerken 2008). To create an instance with $9$ extremal and $n-9$ inner points, for $n=9,\ldots,22$, run

```for n in {9..22}; do python test_planar_6holes.py $n; done```

Similar as the program "test_ES.py", the created SAT instances can be solved and verified using CaDiCaL and DRAT-trim, respectively:

```
for n in {9..22}; do cadical _planar_6holes_n$n.in _planar_6holes_n$n.proof -q; done
for n in {9..22}; do drat-trim _planar_6holes_n$n.in _planar_6holes_n$n.proof -w; done
```

## Download

Programs:

*   The program "test_ES.py" for generating a SAT instance for k-gons and k-holes any dimension \[[download](test_ES.py)\]
*   The program "test_planar_6holes.py" for generating a SAT instance for planar 6-holes \[[download](test_planar_6holes.py)\]
*   The program "test_ES_parse_cadical_sol.py" for reading the chirotope from the output of CaDiCaL (in case of satisfiability) \[[download](test_ES.py)\]

Witnesses:

*   A set of 12 points in $\mathbb{R}^3$ with no 7-gon \[[download](pointsets/empty0_k7_d3_n12.txt)\]
*   A rank 4 chirotope on 12 elements with no 7-gon \[[download](chirotopes/empty0_k7_r4_n12.chi)\]
*   A rank 4 chirotope on 17 elements with no 8-gon \[[download](chirotopes/empty0_k8_r4_n17.chi)\]
*   A rank 4 chirotope on 13 elements with no 7-hole \[[download](chirotopes/empty1_k7_r4_n13.chi)\]
*   A rank 4 chirotope on 18 elements with no 8-hole \[[download](chirotopes/empty1_k8_r4_n18.chi)\]
*   A rank 5 chirotope on 12 elements with no 8-gon \[[download](chirotopes/empty0_k8_r5_n12.chi)\]
*   A rank 6 chirotope on 12 elements with no 9-gon \[[download](chirotopes/empty0_k9_r6_n12.chi.zip)\]
