# Cryptol as an SMT Frontend

At Galois, we've run into [NCC's Cryptography Group] numerous times, because Galois' services and NCC's complement each other extremely well. For example in the ['blst' cryptographic library](https://medium.com/supranational/introducing-blst-2b6a988d68ee) project from [Supranational](https://www.supranational.net/), [Ethereum Foundation](https://ethereum.org/en/) and [Protocol Labs](https://protocol.ai/), NCC provided a [public audit and report](https://research.nccgroup.com/2021/01/20/public-report-blst-cryptographic-implementation-review/), while we at Galois have [verified much of the core library](https://galois.com/blog/2020/09/announcing-the-blst-bls-verification-project/).

When I saw a recent post by [Gérald Doussot](https://research.nccgroup.com/author/geralddoussot/) ([twitter](https://twitter.com/gerald_doussot?lang=en)) titled [Software Verification and Analysis using Z3](https://research.nccgroup.com/2021/01/29/software-verification-and-analysis-using-z3/) I was pretty excited. It turned out to be a great article! The team definitely understands where they can get mileage using 
SMT solvers such as Z3.

An ongoing research area at Galois involves building tools that help engineers interface with SMT solvers, especially in the world of Cryptography. In the NCC article, they use [SMT-LIB](http://smtlib.cs.uiowa.edu/) directly but also say

> Z3 has several, perhaps more approachable APIs available, including in the Python language.

[Cryptol, a tool developed at Galois is one such interface. And for me, it's what I reach for when I need to do work like what's shared in the NCC post.

Cryptol provides, among other things
 - Approachable syntax 
 - Strongly typed length-dependent sequences, allowing static guarantees of program safety
 - First-class functions, which makes it easy to build abstractions.

From here on, this post was written live as I programmed the first half of Gérald's post in Cryptol. If you'd like to see the completed code, you can find it [here](quic.cry). If you'd like to, you can follow along. I've included all of the commands I use to run the program. You'll need to [get Cryptol](https://cryptol.net/downloads.html) first. 

## Reproducing the Demo 

Gérald's post starts with a demo. Find values for ```x``` and ```y``` such that ```x + y = 5```

Let's create a file  ```quic.cry```. In cryptol
solvers reason about functions into the ```Bit``` types (a single bit of data, like a boolean), so we'll make one of those that takes two variables and tells us if adding them together gives 5.

```
sum_eq_5 x y = x + y == 5
```
Save that one line into the file, then in the terminal:

```
$ cryptol quic.cry
```

That loads the file and typechecks it, now we need to tell it what we want the solver to do. In the repl type

```
:sat sum_eq_5
```

That command askes for all of the variables to be satisfied. I got

```
Main> :sat sum_eq_5 
Satisfiable
sum_eq_5 5 0 = True
```

To show off, we can also [curry](https://en.wikipedia.org/wiki/Currying) values in Cryptol, so if I want to fix the value of x I can do that:

```
Main> :sat sum_eq_5 3
Satisfiable
sum_eq_5 3 2 = True
```

Let's take a look at the formulation used by NCC group in SMT-LIB:

```
; this is a comment - it is ignored by solvers

; declare x as integer
(declare-const x Int)

; declare y as an integer
(declare-const y Int)

; express the problem - e.g. add the formula to the list of formulas we are trying to prove
(assert (= (+ x y) 5)) 

; query the solver to determine if the SMT problem is satisfiable
(check-sat) 

; if it is, show one possible solution
(get-model) 
```

and here's what the solution looked like

```
sat
(model 
  (define-fun y () Int
    0)
  (define-fun x () Int
    5)
)
```

That's remarkable similar to what's going on under the hood in Cryptol! We can actually
see what Cryptol is doing if we set the prover to "offline" which outputs an SMT-LIB file 

```
Main> :set prover=offline
Main> :sat sum_eq_5 6
; Some boilerplate...
(define-fun s3 () Int 5)
(declare-fun s0 () Int)
(declare-fun s1 () Int)
(define-fun s2 () Int (+ s0 s1))
(define-fun s4 () Bool (= s2 s3))
(assert s4)
(check-sat)
```

If you compare the handwritten SMT-LIB to the Cryptol, you'll notice that Cryptol uses a lot more definitions. This is because Cryptol agressively breaks down expressions and shares them where possible. For many applications this makes representations far more efficient!

## Checking the QUIC DecodePacketNumber Function

In this section, we're going to implement the ```DecodePacketNumber``` function. Then
we'll constrain the inputs and outputs as required by the specification, and
see if the algoritm suggested by the specification meets those constraints.

I'm going to skip all of the explanation of what the function does. [The NCC article](https://research.nccgroup.com/2021/01/29/software-verification-and-analysis-using-z3/) does a great job of explaining that part. I'm just going to reproduce the SMT work. 

Here's the code snippet that was analyzed. I'll port this to Cryptol. I think it'll be easier to use this version than the SMT-LIB version from the article, because I haven't used SMT-LIB very much. 

```
DecodePacketNumber(largest_pn, truncated_pn, pn_nbits):
  expected_pn  = largest_pn + 1
  pn_win       = 1 << pn_nbits
  pn_hwin      = pn_win / 2
  pn_mask      = pn_win - 1
  # The incoming packet number should be greater than
  # expected_pn - pn_hwin and less than or equal to
  # expected_pn + pn_hwin
  #
  # This means we can't just strip the trailing bits from
  # expected_pn and add the truncated_pn because that might
  # yield a value outside the window.
  #
  # The following code calculates a candidate value and
  # makes sure it's within the packet number window.
  candidate_pn = (expected_pn & ~pn_mask) | truncated_pn
  if candidate_pn <= expected_pn - pn_hwin:
     return candidate_pn + pn_win
  # Note the extra check for underflow when candidate_pn
  # is near zero.
  if candidate_pn > expected_pn + pn_hwin and
     candidate_pn > pn_win:
     return candidate_pn - pn_win
  return candidate_pn
  ```

The article starts with a bunch of limits on the input, in the case of Cryptol we'll
save those for the properties we specify at the end. This will let us distinguish
between adversarial and non-adversarial environments as we check properties.

Let's set up the function type. The article used 64 bit bitvectors, which seems like a good choice.

```
DecodePacketNumber : [64] -> [64] -> [64] -> [64]
```

3 64 bit sequences in, and 1 out. Perfect. Cryptol's type system enforces that ```DecodePacketNumber``` must only take sequences that are 64 bits long. Otherwise the type system will complain. 

Cryptol uses ```where``` which might seem a little upside-down. Here we're saying that there's
some value called result, that we define after the ```where``` keyword.

```
DecodePacketNumber : [64] -> [64] -> [64] -> [64]
DecodePacketNumber largest_pn truncated_pn pn_nbits = result where
   result = 0
```

Sometimes it's nice to set results to ```0``` or ```undefined``` to see if they type-check. If you already loaded the file in the repl it's easy to reload once it's been changed on disk:

```
Main> :r
Loading module Cryptol
Loading module Main
```

It typechecked! Let's fill in the rest of the functionality. Most of it is copy-paste from the reference.
We mess with the names a little, since Cryptol is functional and it can be confusing to rebind names.

When I was copy-pasting, I forgot that ```|``` wasn't in Cryptol. The post says it's bitwise or. I think it's ```||```. Let's check:

```
Cryptol> :? ||

    (||) : {a} (Logic a) => a -> a -> a

Precedence 40, associates to the right.

Logical 'or' over bits. Extends element-wise over sequences, tuples.
```

that's what we want. Same for "and".

Here's a version of the function that typechecks, I'm not sure if it's right yet:

```
DecodePacketNumber : [64] -> [64] -> [64] -> [64]
DecodePacketNumber largest_pn truncated_pn pn_nbits = result where
    expected_pn  = largest_pn + 1
    pn_win       = 1 << pn_nbits
    pn_hwin      = pn_win / 2
    pn_mask      = pn_win - 1
    candidate_pn = (expected_pn && ~pn_mask) || truncated_pn
    result = if candidate_pn <= expected_pn - pn_hwin
             then candidate_pn + pn_win
             else if candidate_pn > expected_pn + pn_hwin /\ candidate_pn > pn_win
                  then candidate_pn - pn_win
                  else candidate_pn
```

The article does some division, but uses a shift with an offset. I think Cryptol division should work fine here (it might be implemented that way internally, I don't know).

Our ```if``` statements look a little different than the ifs in the reference. That's because Cryptol is a functional lanugage, and there is no concept of a statement. In C, you might
be used to updating values and calling functions in a sequence, each separated by a semicolon. The right hand side of those sequences are expressions. Functional languages, such as Cryptol, consist almost entirely of expressions, and have no statements at all.
So, for example, a Cryptol if expression is much more like a conditional operator than an if statement in C.

The reference has a single test case (probably not enough for a function with this much branching behavior). Let's try it out. We'll program the test
vector in Cryptol:

```
DecodePacketNumber_test1 = DecodePacketNumber (0 # 0xa82f30ea) (0 # 0x9b32) 16
DecodePacketNumber_test1_correct = DecodePacketNumber_test1 == (0 # 0xa82f9b3)
```
It's nice to write the test separately so that if the test fails we can see 
the result. I'm sure we won't need that though.

```
Main> DecodePacketNumber_test1_correct
False
```
Noooooooo. Time to bug hunt. We'll run the program and see what we get.

```
Main> DecodePacketNumber_test1
0x00000000a82f9b32
```

Uhh weird. That looks like the result we expected but multiplied by 16 + 2... or a copy paste error. Whoops, our implementation is fine after all, as is the one in the article. Just the article's quote of the spec was off (The original post has been fixed since). We'll add that 2 on the back of
our test checker and everything's happy!

In the article, Z3 spits out all of the intermediate values. We don't do that in
Cryptol because it would usually be pretty hard to filter out what's useful. Could
be a cool future opportunity for debugging though!

Let's encode some of the conditions around the function now. For example
```truncated-pn``` has a max of ```2**32-1```:

```
truncated_pn_max tpn = tpn <= 2^^32-1
```

There's more input requirements, so we write those down as well.
There's also an output requirement, which is that the result does not exceed ```2^^62-1```.

```
result_max result = result <= 2^^62-1
```

I'm going to diverge a bit from the post here because I LIKE TO VERIFY. That is, rather than asking the solver for an example of the condition being violated,
I'm going to ask it if the program can _never_ violate the condition. It's 
actually almost the same question to ask, and the result will be exactly the same.

Putting it all together we get:

```
decode_packet_number_correct fn largest_pn truncated_pn pn_nbits =
    (truncated_pn_max truncated_pn /\
     largest_pn_max largest_pn /\
     largest_pn_min largest_pn /\
     pn_nbits_vals pn_nbits /\
     truncated_bn_range truncated_pn pn_nbits) ==>
     result_max (fn largest_pn truncated_pn pn_nbits)
```

It's worth noting that Cryptol has first-class functions, just like Haskell, Python, and JavaScript. That means that a function or property can take another function as an argument.You can see that we actually
parameterize this property over functions with the same signature as ```DecodePacketNumber```. This will be useful when we fix the function in a minute!

Let's try to prove that the function meets the specification:

```
Main> :prove decode_packet_number_correct DecodePacketNumber
Counterexample
decode_packet_number_correct DecodePacketNumber
  0x3ffffffffeb2f6ad 0x000000007d2941d6 0x0000000000000020 = False
```
We got a counterexample. Not the one that the NCC article calls out as less interesting. I won't go through the exercise of eliminating cases one at a time, but we can do them in the same way as the article by restricting the inputs or outputs in the spec.

We can also try fixing the function. In the full file that's called ```DecodePacketNumberFixed```. Checking that we get

```
Main> :prove decode_packet_number_correct DecodePacketNumberFixed 
Counterexample
decode_packet_number_correct DecodePacketNumberFixed
  0x3fffffffffffffff 0x0000000000000015 0x0000000000000008 = False
```

Huh. It seems like this failure case might be a mistake of the precondition being
too permissive with the range on the first argument. I can't claim to understand the function well enough to know if this is actually a bug.

If we update the precondition we get:

```
Main> :prove decode_packet_number_correct DecodePacketNumberFixed 
Q.E.D.
```

Which means the property holds! 
 
## Wrapping up

Overall, this went really smoothly. The specification ported over nicely to Cryptol, with the only change being adapting slightly to the functional style. We
were able to keep our propreties separate from the implementation, which will let us
use them separately later. Or to reuse the properties with different implementations.

Cryptol also allowed us to work directly with hex values, which let us copy test cases directly from the spec. I plan on following this post with the Finite Field Arithmetic Verification that makes up the second aprt of the NCC post. I hope it goes as well as this one did.