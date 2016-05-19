--------------- MODULE test204 -------------

(***************************************************************************)
(* Test definability and use of all user-defined operators as prefix       *)
(* operators, as in +(a, b).  It does not work with binary minus.          *)
(***************************************************************************)

z - y == <<1, z, y>>
\* ASSUME -(4, 6) = <<1, 4, 6>>
z + y == <<2, z, y>>
ASSUME +(4, 6) = <<2, 4, 6>>
z * y == <<3, z, y>>
ASSUME *(4, 6) = <<3, 4, 6>>
z / y == <<4, z, y>>
ASSUME /(4, 6) = <<4, 4, 6>>
z ^ y == <<5, z, y>>
ASSUME ^(4, 6) = <<5, 4, 6>>
z < y == <<6, z, y>>
ASSUME <(4, 6) = <<6, 4, 6>>
z > y == <<7, z, y>>
ASSUME >(4, 6) = <<7, 4, 6>>
z .. y == <<8, z, y>>
ASSUME ..(4, 6) = <<8, 4, 6>>
z ... y == <<9, z, y>>
ASSUME ...(4, 6) = <<9, 4, 6>>
z | y == <<10, z, y>>
ASSUME |(4, 6) = <<10, 4, 6>>
z || y == <<11, z, y>>
ASSUME ||(4, 6) = <<11, 4, 6>>
z & y == <<12, z, y>>
ASSUME &(4, 6) = <<12, 4, 6>>
z && y == <<13, z, y>>
ASSUME &&(4, 6) = <<13, 4, 6>>
z $ y == <<14, z, y>>
ASSUME $(4, 6) = <<14, 4, 6>>
z $$ y == <<15, z, y>>
ASSUME $$(4, 6) = <<15, 4, 6>>
z ?? y == <<16, z, y>>
ASSUME ??(4, 6) = <<16, 4, 6>>
z %% y == <<17, z, y>>
ASSUME %%(4, 6) = <<17, 4, 6>>
z ## y == <<18, z, y>>
ASSUME ##(4, 6) = <<18, 4, 6>>
z ++ y == <<19, z, y>>
ASSUME ++(4, 6) = <<19, 4, 6>>
z -- y == <<20, z, y>>
ASSUME --(4, 6) = <<20, 4, 6>>
z ** y == <<21, z, y>>
ASSUME **(4, 6) = <<21, 4, 6>>
z // y == <<22, z, y>>
ASSUME //(4, 6) = <<22, 4, 6>>
z ^^ y == <<23, z, y>>
ASSUME ^^(4, 6) = <<23, 4, 6>>
z @@ y == <<23, z, y>> 
ASSUME @@(4, 6) = <<23, 4, 6>>
z !! y == <<24, z, y>>
ASSUME !!(4, 6) = <<24, 4, 6>>
z |- y == <<25, z, y>>
ASSUME |-(4, 6) = <<25, 4, 6>>
z |= y == <<26, z, y>>
ASSUME |=(4, 6) = <<26, 4, 6>>
z -| y == <<27, z, y>>
ASSUME -|(4, 6) = <<27, 4, 6>>
z =| y == <<28, z, y>>
ASSUME =|(4, 6) = <<28, 4, 6>>
z <: y == <<29, z, y>>
ASSUME <:(4, 6) = <<29, 4, 6>>
z :> y == <<29, z, y>>
ASSUME :>(4, 6) = <<29, 4, 6>>
z := y == <<30, z, y>>
ASSUME :=(4, 6) = <<30, 4, 6>>
z ::= y == <<31, z, y>>
ASSUME ::=(4, 6) = <<31, 4, 6>>
z \uplus y == <<32, z, y>>
ASSUME \uplus(4, 6) = <<32, 4, 6>>
z \sqcap y == <<33, z, y>>
ASSUME \sqcap(4, 6) = <<33, 4, 6>>
z \sqcup y == <<34, z, y>>
ASSUME \sqcup(4, 6) = <<34, 4, 6>>
z \div y == <<35, z, y>>
ASSUME \div(4, 6) = <<35, 4, 6>>
z \wr y == <<36, z, y>>
ASSUME \wr(4, 6) = <<36, 4, 6>>
z \star y == <<37, z, y>>
ASSUME \star(4, 6) = <<37, 4, 6>>
z \bigcirc y == <<38, z, y>>
ASSUME \bigcirc(4, 6) = <<38, 4, 6>>
z \bullet y == <<39, z, y>>
ASSUME \bullet(4, 6) = <<39, 4, 6>>
z \prec y == <<40, z, y>>
ASSUME \prec(4, 6) = <<40, 4, 6>>
z \succ y == <<41, z, y>>
ASSUME \succ(4, 6) = <<41, 4, 6>>
z \preceq y == <<42, z, y>>
ASSUME \preceq(4, 6) = <<42, 4, 6>>
z \succeq y == <<43, z, y>>
ASSUME \succeq(4, 6) = <<43, 4, 6>>
z \sim y == <<44, z, y>>
ASSUME \sim(4, 6) = <<44, 4, 6>>
z \simeq y == <<45, z, y>>
ASSUME \simeq(4, 6) = <<45, 4, 6>>
z \ll y == <<46, z, y>>
ASSUME \ll(4, 6) = <<46, 4, 6>>
z \gg y == <<47, z, y>>
ASSUME \gg(4, 6) = <<47, 4, 6>>
z \asymp y == <<48, z, y>>
ASSUME \asymp(4, 6) = <<48, 4, 6>>
z \subset y == <<49, z, y>>
ASSUME \subset(4, 6) = <<49, 4, 6>>
z \supset y == <<50, z, y>>
ASSUME \supset(4, 6) = <<50, 4, 6>>
z \supseteq y == <<51, z, y>>
ASSUME \supseteq(4, 6) = <<51, 4, 6>>
z \approx y == <<52, z, y>>
ASSUME \approx(4, 6) = <<52, 4, 6>>
z \cong y == <<53, z, y>>
ASSUME \cong(4, 6) = <<53, 4, 6>>
z \sqsubset y == <<54, z, y>>
ASSUME \sqsubset(4, 6) = <<54, 4, 6>>
z \sqsupset y == <<55, z, y>>
ASSUME \sqsupset(4, 6) = <<55, 4, 6>>
z \sqsubseteq y == <<56, z, y>>
ASSUME \sqsubseteq(4, 6) = <<56, 4, 6>>
z \sqsupseteq y == <<57, z, y>>
ASSUME \sqsupseteq(4, 6) = <<57, 4, 6>>
z \doteq y == <<58, z, y>>
ASSUME \doteq(4, 6) = <<58, 4, 6>>
z \propto y == <<59, z, y>>
ASSUME \propto(4, 6) = <<59, 4, 6>>

z ^+ == <<60, z>>
ASSUME ^+(4) = <<60, 4>>
z ^* == <<61, z>>
ASSUME ^*(4) = <<61, 4>>
z ^# == <<62, z>>
ASSUME ^#(4) = <<62, 4>>
-. z == <<63, z>>
ASSUME -.(4) = <<63, 4>>

z \leq y == <<64, z, y>>
ASSUME \leq(4, 6) = <<64, 4, 6>>
ASSUME <=(4, 6) = <<64, 4, 6>>
ASSUME =<(4, 6) = <<64, 4, 6>>

z \geq y == <<65, z, y>>
ASSUME \geq(4, 6) = <<65, 4, 6>>
ASSUME >=(4, 6) = <<65, 4, 6>>

z \oplus y == <<66, z, y>>
ASSUME \oplus(4, 6) = <<66, 4, 6>>
ASSUME (+) (4, 6) = <<66, 4, 6>>

z \ominus y == <<67, z, y>>
ASSUME \ominus(4, 6) = <<67, 4, 6>>
ASSUME (-) (4, 6) = <<67, 4, 6>>


z \odot y == <<68, z, y>>
ASSUME \odot(4, 6) = <<68, 4, 6>>
ASSUME (.) (4, 6) = <<68, 4, 6>>

z \otimes y == <<69, z, y>>
ASSUME \otimes(4, 6) = <<69, 4, 6>>
ASSUME (\X) (4, 6) = <<69, 4, 6>>

z \oslash y == <<70, z, y>>
ASSUME \oslash(4, 6) = <<70, 4, 6>>
ASSUME (/) (4, 6) = <<70, 4, 6>>

z \circ y == <<71, z, y>>
ASSUME \circ(4, 6) = <<71, 4, 6>>
ASSUME \o (4, 6) = <<71, 4, 6>>

ASSUME \in(1, {1})

ASSUME \cup({1}, {2}) = {1,2}

=============================================================================
