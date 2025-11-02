# er-hash-consing
effecient hash consing for given type grammar in erlang

The goal of this project is to extend hashing mechanism of sharesem with a hash function that maps name-equivalent types to the same hash value. 
Example:

```erlang
hash({X1 = true | (X1, X1)}) = hash({X2 = true | (X3, X3), X3 = true | (X3, X3)})
```


## Resources:

* Maziarz, Krzysztof, et al. "Hashing modulo alpha-equivalence." Proceedings of the 42nd ACM SIGPLAN International Conference on Programming Language Design and Implementation. 2021.

* Filliâtre, Jean-Christophe, and Sylvain Conchon. "Type-safe modular hash-consing." Proceedings of the 2006 Workshop on ML. 2006.

* Considine, Jeffrey. Efficient hash-consing of recursive types. Boston University Computer Science Department, 2000.

* https://github.com/albsch/minsem/blob/master/apps/01minsem/src/minsem.erl

* https://github.com/albsch/minsem/blob/master/apps/04sharesem/src/sharesem.erl

## Notes:

* The recursive equation names (e.g. $X_1$) are function references in `minsem` and of type `ty_ref()` in `sharesem`.

## Deliverables:

* Hashsem implementation in Erlang
* At least for the following co-inductively defined type grammar: $\tau = true | (\tau, \tau) | \tau ∪ \tau | !\tau$
* Test cases which show-case sharing of recursive types
