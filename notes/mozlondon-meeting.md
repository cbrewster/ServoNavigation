# MozLondon session history meeting 2016-06-15

## Gecko model

Gecko uses a different model of session hostory, kept as a
list of trees. It uses cloning and tree diffing for navigation
and traversal.

## Navigation deleting history

Gecko (and probably the other browsers) delete more history on navigation
(and posibly on traversal). This may allow us to maintain some invariants
on the session history so we avoid some of the counterexamples.

## Tests

It would be useful to expand our list of test cases.

Issue: to enforce cross-test isolation, tests should be run in
a new top-level browsing context (otherwise navigating back in test *i*+1
can end up back in test *i*. This may be a problem for Servo, unless
the wpt tests are run in browser.html.
