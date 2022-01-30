# TNT: a Transformation for analyzing Narrowing Termination

**TNT** is a tool to analyze the termination of narrowing. It takes a term-rewriting system (TRS) and a sequence of abstract terms that specify which arguments are ground for some user-defined functions; for instance, the abstract term ```append(g,v)``` specifies that the first argument of function ```append``` is ground and the second one is possibly a variable. 

This is similar to the notion of "modes" in logic programming. The transformation then proceeds basically as follows:

* First, a "safe" argument filtering is inferred, i.e., a mapping that specifies which are the ground arguments of every user-defined function in every possible narrowing computation (starting from any possible instance of the abstract term).

* Then, the TRS is transformed so that only the ground arguments of user-defined functions remain and, most importantly, so that the termination of the transformed TRS implies the termination of the original TRS.

Therefore, once the (possibly) non-ground arguments are filtered away, the termination of the transformed program can be analyzed with any termination prover for TRSs, like [AProVE](https://aprove.informatik.rwth-aachen.de/).

A more detailed account of the technique can be found in this paper: 

Naoki Nishida, Germán Vidal:
[Termination of narrowing via termination of rewriting](https://link.springer.com/article/10.1007/s00200-010-0122-4). Appl. Algebra Eng. Commun. Comput. 21(3): 177-225 (2010)

In order to use **TNT**, you need [SWI Prolog](https://www.swi-prolog.org/). A typical session looks as follows:

<div>
<pre>
$ swipl
Welcome to SWI-Prolog (threaded, 64 bits, version 8.2.4)
SWI-Prolog comes with ABSOLUTELY NO WARRANTY. This is free software.
Please run ?- license. for legal details.

For online help and background, visit https://www.swi-prolog.org
For built-in help, use ?- help(Topic). or ?- apropos(Word).

?- [tnt].
true.

?- trans('examples/AG01/#3.12.trs',[filter('app(g,v)')]).
(from AG01 3.12)
(VAR x y n)
(RULES
app(nil) -> nullVar
app(add(n,x)) -> add(n,app(x))
reverse(nil) -> nil
reverse(add(n,x)) -> app(reverse(x))
shuffle(nil) -> nil
shuffle(add(n,x)) -> add(n,shuffle(reverse(x)))
)
(COMMENT TRS filtered for: shuffle(g), reverse(g), app(g,v))
true.
</div>
If you prefer to save the output to a file, you can use

```
?- trans('examples/AG01/#3.12.trs',[filter('app(g,v)'),output('temp.trs')]).
```
instead.

If you prefer to use the tool as a shell command, you only need to add

```
#!/usr/bin/env swipl  
:- initialization go_cli,halt.
```
at the beginning of the file ```tnt.pl```. This is already done in file ```trans.pl```. Then, it can be used as follows:

``
$ ./trans.pl 'examples/AG01/#3.12.trs' -f 'app(g,v)'
``

or 

``
$ ./trans.pl 'examples/AG01/#3.12.trs' -f 'app(g,v)' -o 'temp.trs'
``

if you prefer to save the output to a file.

Please send me questions or comments to <gvidal@dsic.upv.es> .