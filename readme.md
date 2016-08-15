# Servo Navigation Proposal

This repo contains notes on the design of Servo's navigation model.

The full document is [notes.pdf](notes/notes.pdf), and includes:

 - A navigation history model based on the WHATWG specification.
 - A series of counter-examples showing unexpected behaviour of the WHATWG model.
 - A series of patches for each of the counter-examples.
 - A proof (mechanized in Agda) that the patched model satisfies the **fundamental property**: that traversing the session history by δ then by δ′ is the same as traversing by (δ + δ′).
 - Experimental evidence that browser implementations are closer to the patched model than to the original.

The implementation in Servo is part of the [constellation](https://github.com/servo/servo/blob/master/components/constellation/constellation.rs).

[![Creative Commons License](http://i.creativecommons.org/l/by/4.0/88x31.png)](http://creativecommons.org/licenses/by/4.0/)
This work is licensed under a [Creative Commons Attribution 4.0 International License](http://creativecommons.org/licenses/by/4.0/).
