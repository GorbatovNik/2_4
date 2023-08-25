Grammar -> {Declaration}.
Declaration -> "$AXIOM" NTERM | "$NTERM" NTERM {NTERM} | "$TERM" TERM {TERM} | "$RULE" NTERM ASSIGN Expr.
Expr -> Expr Expr | NTERM | TERM | Expr "|" Expr | "{" Expr "}" | "(" Expr ")".
-----------------------------------------------------------------------------------
Grammar -> AxiomDecl Grammar | NtermsDecl Grammar | TermsDecl Grammar | RuleDecl Grammar | .
AxiomDecl -> "$AXIOM" NTERM.
NtermsDecl -> "$NTERM" NTERM NtermListOpt.
TermsDecl ->  "$TERM" TERM TermListOpt.
RuleDecl ->  "$RULE" NTERM ASSIGN Expr.
NtermListOpt -> NTERM NtermListOpt | .
TermListOpt -> TERM TermListOpt | .
Expr -> Expr ALTERN Altern | Altern.
Altern -> Altern Concat | Concat.
Concat -> NTERM | TERM | LPAREN Expr RPAREN | LPAREN_CURVE Expr RPAREN_CURVE.
-----------------------------------------------------------------------------------
EBNF:

Grammar = {Declaration}.
Declaration = AxiomDecl | NtermsDecl | TermsDecl | RuleDecl.
AxiomDecl = "$AXIOM" NTERM.
NtermsDecl = "$NTERM" NTERM {NTERM}.
TermsDecl = "$TERM" TERM {TERM}.
RuleDecl = "$RULE" NTERM ASSIGN Expr.
Expr = Altern {ALTERN Altern}.
Altern = Concat {Concat}.
Concat = NTERM | TERM | Grouping | Option.
Grouping =  LPAREN Expr RPAREN.
Option = LPAREN

CURVE Expr RPAREN_CURVE.