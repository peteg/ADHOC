Oleg, http://okmij.org/ftp/Haskell/Mr-S-P.lhs

Solving the "Mr.S and Mr.P" puzzle by John McCarthy:

	Formalization of two Puzzles Involving Knowledge
	McCarthy, John (1987).
	http://www-formal.stanford.edu/jmc/puzzles.html

We pick two numbers a and b, so that a>=b and both numbers are within
the range [2,99]. We give Mr.P the product a*b and give Mr.S the sum
a+b.

The following dialog takes place:

	Mr.P: I don't know the numbers
	Mr.S: I knew you didn't know. I don't know either.
	Mr.P: Now I know the numbers
	Mr.S: Now I know them too

Can we find the numbers a and b?


The following is a literate Haskell code. It can be loaded as it is in
Hugs or GHCi. It takes a while to compute; the optimizations are
straightforward; yet we deliberately chose the simplest code. A
compiled version should be faster.

Chung-chieh Shan has pointed out the paper
   Hans P. van Ditmarsch, Ji Ruan and Rineke Verbrugge
   Sum and Product in Dynamic Epistemic Logic
   Journal of Logic and Computation, 2008, v18, N4, pp.563--588.

that discusses at great extent the history of the riddle, its
modeling in modal `public announcement logic', and solving using
epistemic model checkers.


> module MrSP where

First, let's define good numbers

> good_nums = [2..99]::[Int]

Given a number p, find all good factors a and b (a>=b)
and return them (the pairs of them) in a list. We use the obvious and
straightforward memoization (tabling):

> good_factors_table = map gf [0..]
>  where
>   gf p = [ (a,b) | a<-good_nums, b<-good_nums, a >= b, a*b==p ]

> good_factors p = good_factors_table !! p

Given a number s, find all good summands a and b (a>=b)
and return the pairs of them in a list

> good_summands_table = map gs [0..]
>  where
>   gs s = [ (a,b) | a<-good_nums, b<-good_nums, a >= b, a+b==s ]

> good_summands s = good_summands_table !! s


> -- Test if a list is a singleton
> singleton_p [_] = True
> singleton_p _   = False

Let's encode the first fact: Mr.P doesn't know the numbers.
Mr. P would have known the numbers if the product had had a unique good
factorization

> fact1 (a,b) = not (singleton_p $ good_factors $ a*b)

Let's encode the second fact: Mr.S doesn't know the numbers

> fact2 (a,b) = not (singleton_p $ good_summands $ a+b)

Let's encode the third fact: Mr.S knows that Mr.P doesn't know the numbers.
In other words, for all possible summands that make a+b, Mr.P cannot be
certain of the numbers

> fact3 (a,b) = all fact1 (good_summands $ a+b)

Let's encode the fourth fact: Mr.P _now_ knows that fact3 is true
and is able to find the numbers. That is, of all factorizations
of a*b there exists only one that makes fact3 being true.

> fact4 (a,b) =  singleton_p $ filter fact3 (good_factors $ a*b)

The fifth fact is that Mr.S. knows that Mr.P found the numbers:
of all the possible decompositions of a+b, there exists only one that
makes fact4 true.

> fact5 (a,b) = singleton_p $ filter fact4 (good_summands $ a+b)

Finally, we compute the list of all numbers such that fact1..fact5
hold:

> result = [(a,b) | a<-good_nums, b<-good_nums, a >= b,
>	    all ($ (a,b)) [fact1,fact2,fact3,fact4,fact5] ]

The answer is
*Main> result
[(13,4)]

That is, a unique answer. Note how Haskell notation is concise,
compared to the one employed in the paper by McCarthy.
