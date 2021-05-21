# Cryptographic assurance with Cryptol

Field arithemetic code is important and has edge cases
lurking everywhere. Cryptol is a tool that can gurantee
you've got the edge cases right!

In this post, we continue reproducing an [NCC Group Post]()
about programming in z3. In our [last post]() we checked
the implementation of part of the QUIC protocol. In this
post we'll explore an optimized implementation of field
arithemetic. 

I'd love it if you [installed Cryptol](https://cryptol.net/downloads.html)
and worked along, but I've reproduced everything here, so I'll forgive you
if you don't.

I'm also going to take you through a mistake I actually made in the specification
and explain how I debugged it. I promise I really made this mistake, I didn't just
put it in there to make you feel good.

## I can't believe you've done this

The whole point of this exercise is that code isn't all that efficient
unless it uses the built-in mathematical operations. On most of our computers
today the biggest numbers those work on are 64 bits long. When we need
to do math operations on bigger numbers, we're forced to introduce risk
into our code. Cryptol can help mitigate that risk.

If I want to do math on 256 bit numbers, I've got a couple of choices

- Build up some lists of bits (usually booleans) in my language, along with operations on them (bitvector approach)
- Map those operations onto the numbers that the computer represents

The first is far easier to get right, you get to treat your numbers uniformly, so you have
far fewer edge cases to deal with. Unfortunately, it's also impermissibly slow and memory
intensive. In many cases you'll end up using 8/16 times as much memory to represent your
bitvectors as you would using the comptuer representations.

That means that for most high performance uses, we'll need to map operations onto machine
numbers. Bignum libraries such as GMP can do this reasonably well, but they're generalized
and performance can often still be improved for specific applications.

## Setting up the types

The NCC post shows some go code, we're going to work from the same code. Our
goal is to implement this algorithm in Cryptol and show that it's equivalent
to a simpler operation over bigger bitvectors.

```
// Internal function for field addition.
// Parameters:
//   d    destination
//   a    first operand
//   b    second operand
//   mq   modulus definition parameter
func gf_add(d, a, b *[4]uint64, mq uint64) {
	// First pass: sum over 256 bits + carry
	var cc uint64 = 0
	for i := 0; i < 4; i ++ {
		d[i], cc = bits.Add64(a[i], b[i], cc)
	}

	// Second pass: if there is a carry, subtract 2*p = 2^256 - 2*mq;
	// i.e. we add 2*mq.
	d[0], cc = bits.Add64(d[0], (mq << 1) & -cc, 0)
	for i := 1; i < 4; i ++ {
		d[i], cc = bits.Add64(d[i], 0, cc)
	}

	// If there is an extra carry, then this means that the initial
	// sum was at least 2^257 - 2*mq, in which case the current low
	// limb is necessarily lower than 2*mq, and adding 2*mq again
	// won't trigger an extra carry.
	d[0] += (mq << 1) & -cc
}

func gf_sub(d, a, b *[4]uint64, mq uint64) {
	// First pass: difference over 256 bits + borrow
	var cc uint64 = 0
	for i := 0; i < 4; i ++ {
		d[i], cc = bits.Sub64(a[i], b[i], cc)
	}

	// Second pass: if there is a borrow, add 2*p = 2^256 - 2*mq;
	// i.e. we subtract 2*mq.
	d[0], cc = bits.Sub64(d[0], (mq << 1) & -cc, 0)
	for i := 1; i < 4; i ++ {
		d[i], cc = bits.Sub64(d[i], 0, cc)
	}

	// If there is an extra borrow, then this means that the
	// subtraction of 2*mq above triggered a borrow, and the first
	// limb is at least 2^64 - 2*mq; we can subtract 2*mq again without
	// triggering another borrow.
	d[0] -= (mq << 1) & -cc
}
```

I like to set up the types, and try to understand how they correlate to numbers first.
Doing this right up front can safe a lot of trouble in the future. 

The inputs are big numbers of size 4*64, we'll give this a type alias so we can
reuse it easily.

```
Type BN = [4][64]
```

That's a transparent alias in Cryptol, ``BN`` can be used interchangibly with ```[4][64]```

We'll state a couple of properties about what that type means. In general, it's meant
to be a way to split up a longer number in to 64 bit chunks. Let's record that, along with a property

```
bn_to_sequence : BN -> [4*64]
bn_to_sequence bn = join bn

sequence_to_bn : [4*64] -> BN
sequence_to_bn seq = split seq

property bn_roundtrip bn = bn == bn_to_sequence (sequence_to_bn bn)
```

The property is a "roundtrip" property, stating that if we encode a long sequence as a BN and then convert
back, we end up back where we started. 

```
Main> :prove bn_roundtrip 
Q.E.D.
(Total Elapsed Time: 0.006s, using "Z3")
```

Woah, that went fast. I bet Cryptol knows some properties about join split and reverse that it can simplify away.

It's good to have these "denotations" for the BV type. They can serve as specs as we start to implement operations.

## Implementing addition with carry

Looks like we're going to need an implementation of ```Bits.add``` before we go further.

```
bits_add : {n} (fin n)=> [n] -> [n] -> Bit -> (Bit,[n])
bits_add x y cin = (z@0, drop z)
  where
  z : [n+1]
  z = zext x + zext y + zext [cin]
```

We can do it as 65 bit addition in Cryptol. If this were the actual function we were specifying we might want to make it look more like the original. We'll do that for the other function. There's some new stuff here too. We see
the ``zext`` function, which makes use of Crytol types to automaically add zeros to the most significant digits in order to make the value the length that cryptol expects it to be. In this case, since we've said ``z`` has length ``n+1`` we know that the arguments to the addition must also have length ``n+1``. We also see the drop function, which drops values from the front, in order to get the right length. In this case, we do that because the carry 
is in the 0th index, but we want to return it separately from the sum.

## Specifying 256 bit addition

With that implemented, we can start to look at the body of the ``gf_add`` function.

The first part of the ``gf_add`` function is doing a straight addition of the two numbers. We'll implement that with the following cryptol:

```
bn_add : BN -> BN -> ([4]Bit, BN)
bn_add a b = (drop cc, d.1)
  where
   cc : [5]Bit
   cc  = [0] # d.0

   d : [4](Bit, [64])
   d@i = bits_add (a@i) (b@i) (cc@i)
```

We got lots of Cryptol here. Let's break it down and explain some things.

```drop cc``` drops the first value in the sequence. That's the initial 0 carry, there's no reason to return it
we really only need the last carry for functionality, but we keep them all for tracking purproses.

```d.1``` takes the second item of tuple (or pair) containing the value and the carry. That matches up with
our ```bits_add``` implementation which returns a pair of the carry and the result

We start our list of all of the carries off with zero, and the build the rest from the 0th indices of
```d```. Cryptol is _wildly_ polymorphic so we can do

```
Main> [(0,1),(2,3)].0
[0, 2]
```

Finally we construct a sequence d, which refers back to the list of carry results.

This is a lot to take in, so let's write a property to be sure we got it right

```
property bn_add_correct x y = sequence_to_bn (bn_to_sequence x + bn_to_sequence y)  == (bn_add x y).1
```

We'll prove it in the REPL

```
Main> :prove bn_add_correrct 
Counterexample
bn_add_correct
  [0b1000000000000000000000000000000000000000000000000000000000000001,
   0b0000000000000000000000001000000000000000000000000000000000000000,
   0b0000100000000000000000000000000000000000000000000000000000000000,
   0b1111111111111011111111111111111111111111111111111111110000000000]
  [0b1111111111111111111111111111111111111111111111111111111111111111,
   0b1111111111111111111111111111111111111111111111111111111111111111,
   0b1111100000000000000000000000000000000000000000000111111111111111,
   0b1111111111111111111111111111111111111111111111111111110000000000] = False
(Total Elapsed Time: 0.072s, using "Z3")
```

Or try to at least. We got something wrong. The counterexample provides an
input that violates the property, but it looks like it'd be hard to figure out what went wrong.
Sometimes a good thing do do is push something simple and concrete to learn more.
Let's add 1 + 1 and see if we can learn more.

```
Main> bn_add_correct (sequence_to_bn (zext 1)) (sequence_to_bn (zext 1))
True
```

Our property is ``True`` for those values so things are partially right at least. Let's try something that triggers a carry, since that's an obvious place we might make a mistake

```
Main> bn_add_correct (sequence_to_bn (zext (1 # (0 : [63])))) (sequence_to_bn (zext (1 # (0 : [63])))) 
False
```

Narrowing it down... let's look at the two sides of our property individually and see if we can spot the problem

```
Main> sequence_to_bn ((zext (1 # (0 : [63]))) + (zext (1 # (0 : [63]))))
Showing a specific instance of polymorphic result:
  * Using '1' for type argument 'front' of '(Cryptol::#)'
  * Using '1' for type argument 'front' of '(Cryptol::#)'
[0b0000000000000000000000000000000000000000000000000000000000000000,
 0b0000000000000000000000000000000000000000000000000000000000000000,
 0b0000000000000000000000000000000000000000000000000000000000000001,
 0b0000000000000000000000000000000000000000000000000000000000000000]
```

Ok that worked pretty well, we can see that the bit carried from the 4th item to the third. Let's try our function
```
Main> bn_add (sequence_to_bn (zext (1 # (0 : [63]))))  (sequence_to_bn (zext (1 # (0 : [63]))))
(0x8,
 [0b0000000000000000000000000000000000000000000000000000000000000000,
  0b0000000000000000000000000000000000000000000000000000000000000000,
  0b0000000000000000000000000000000000000000000000000000000000000000,
  0b0000000000000000000000000000000000000000000000000000000000000000])
```

Oh! The carry went the other way, falling off the end of the operation and returning as a set bit for the final carry (``0x08`` in binary is ``0b1000``).

Now we just need to spend some time thinking about if our spec or implementation is wrong. 

It seems likely that it was our specification. We (look I included you when "we" made a mistake) kind of made an assumption about the representation of ```BN```
before we knew what was intended by the implementation. Looking at the implementation it carries from the 0th
index increasing through the sequence. The carry in our Cryptol addition went the other way though. Byte-ordering
is a notoriously tricky bit of operations like this, and here it is, striking again!.

Let's fix our representation functions.

```
bn_to_sequence : BN -> [4*64]
bn_to_sequence bn =  join (reverse (bn))

sequence_to_bn : [4*64] -> BN
sequence_to_bn seq = reverse (split (seq))
```

We threw a reverse in there becasue the function seems to be looping from zero, carrying up with the index.
That means that the 0th number will be the least significant. Cryptol does have a built in bit-order for
constants and operators. We can check this in the repl

```
Main> (1 : [8]) @ 0
False
Main> (1 : [8]) @ 7
True
```

The least significant digit is at index 7, so we'll get the order wrong if we don't reverse our BN first.

Let's try our proof again and see if that fixed it

```
Main> :prove bn_add_correct 
Q.E.D.
```

All good! On with the post!

## Specifying the gf_add function (finally)

There are two more passes. If there was a carry resulting from the first addition,
we add 2*mq and propigate that. If there's still a carry, we repeat the subtraction,
but this time (the comments say) we don't need to repeat the carry

Now we can define ``gf_add``. We're going to make ``mq`` the first argument though, so we can more easily
set it to a fixed value when we're using it. We're also returning all of the carries.

```
gf_add : [64] -> BN -> BN -> (BN, [8]Bit)
gf_add mq a b = (ds3, ccs1 # ccs2) where
  (ccs1, ds1) = bn_add a b
  (ccs2, ds2) = bn_add ds1 (update zero 0 (((mq : [64]) << 1) && -(zext [(ccs1!0)])))
  ds3 = update ds2 0 (ds2@0 + (((mq : [64]) << 1) && -(zext [(ccs2!0)])))
```

This looks similar to the Go implementation. We have to use subscripts as the variables update them
because Cryptol is functional and doesn't allow you to shadow names. It also looks a bit shorter
than the code in go. One reason is that we pulled the two loops out into the bn_add function.
The other is that because we'd created that function, we removed the special case in the go
code, instead using the ``update`` function in Cryptol to allow us to reuse the code from the first
loop.

One thing I thought a little mistifying was the pattern 

```
(((mq : [64]) << 1) && -(zext [(ccs2!0)])
```

It's being a little tricky with the shift and the mask. I think this is to avoid
introducing side-channels, but we can prove it equivalent to something that
has side channels. We can write a little property:

```
property mq_mask_correct cc mq = ((mq : [64]) << 1) && -(zext [cc]) == if cc then 2 * mq else 0
```

and prove it

```
Main> :prove mq_mask_correct 
Q.E.D.
(Total Elapsed Time: 0.007s, using "Z3")
```

It's nice to do this kind of thing as you go, because if you make a mistake it's helpful to know
what parts are right for sure.

Now that we've got the implementation done we can write a correctness property for it. First let's
write a version of our function that operates on and returns bitvectors:

```
gf_add_bv x y = bn_to_sequence ((gf_add mqc (sequence_to_bn x) (sequence_to_bn y))).0
```

Then we can line it up with an operation over long sequences.

```
property gf_add_correct x y = (((zext x) : [257]) + (zext y)) % pc == (zext (gf_add_bv x y)) % pc
```

We have to do the modulus on both sides because the ``gf_add`` function doesn't fully reduce. This
is a pretty common trick to avoid doing expensive operations until they're actually necessary. 

We can prove it pretty quickly, surprisingly.

```
Main> :prove gf_add_correct 
Q.E.D.
(Total Elapsed Time: 13.243s, using "Z3")
```

The NCC post said it takes a few hours. The difference could either be that Cryptol is leveraging in built in
simplifications, resulting in a better goal for Z3, or that Z3 itself was different between the two 

Nice! All done! Looks like the algorithm is in good shape. Regardless, we've proved an algorithm, not an
implementation. What if someone made a mistake writing this down in C, Rust, or their language of choice?

## Tying it to implementation

There are two ways we could tye a spec like this to an implementation

- Proofs, using a tool like SAW
- Test cases
- Both! (Recommended)

That was 3, I guess. The recommended order (from me) is tests first, then proofs. 

Big words from someone who spends their days writing proofs! Why would I make this recommendation?

Tests give immediate feedback, and every developer already understands how to work with them. This is in
contrasts to proofs, which will often require learning an additional tool or two, along with a paradigm for
reasoning. Tests are generally far quicker to develop than proofs, and easier to update. They also test cover "full stack" and can catch bugs in compilers or even hardware, if bugs exist.

Proofs, on the other hand, will give a higher assurance of correctness, but in general will take longer
and be harder to interact with. In this case, writing a proof of a C program wouldn't be much harder
than the work we just did.

With the implementation we just made, we can automatically generate some tests to cover the behavior various
carry combinations. First we'll define a property that's true if it matches the supplied carry

```
carry_eq p c x y r = p c /\ ((gf_add mqc x y).1 == c) /\ ((gf_add mqc x y).0 == r)
```

We did something a little funny here. We take a _predicate_ on the carries, so we can say
something like "I want a carry pattern where the 0th bit is 1".

We also add an argument ```r``` for convenience

Then we can ask the solver to give us a satisfying input:

```
Main> :sat (carry_eq (\c -> c @ 0 ==True))
Satisfiable
(carry_eq (\c -> c @ 0 == True))
  0x80
  [0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000]
  [0xffff7fffffffffff, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000]
  [0xffff7ffffffffffe, 0x0000000000000001, 0x0000000000000000,
   0x0000000000000000] = True
```

That tells us the arguments supplied to carry_eq, as well as the result! 

It's worth noting again, how much less verbose our approach was than doing things
directly in z3 syntax. Our whole effort took around 50 lines of code (closer to 60 if you cound the commands at the REPL). The z3 implementation took hundreds of lines. 

In general, this is why I prefer interacting with Cryptol to interacting with the solver directly, when I can manage it. Thanks for reading!
