------ MODULE AST -------
EXTENDS TLC
fairness == ""
 
ast == 
[type     |-> "uniprocess", 
 name  |-> "Euclid", 
 decls  |-> <<[var |-> "u_ini", eqOrIn |-> "\\in", val |-> << "1", "..", "MaxNum" >>], 
              [var |-> "v_ini", eqOrIn |-> "\\in", val |-> << "1", "..", "MaxNum" >>], 
              [var |-> "u", eqOrIn |-> "=", val |-> << "u_ini" >>], 
              [var |-> "v", eqOrIn |-> "=", val |-> << "v_ini" >>]>>,
 defs   |-> <<  >>,
 prcds  |-> <<>>,
 body  |-> <<[label |-> "a",
              stmts |-> <<[type    |-> "while", 
                           test    |-> << "u", "#", "0" >>,
                           labDo   |-> <<[label |-> "b",
                                          stmts |-> <<[type |-> "assignment",
                                                       ass  |-> <<[lhs |-> [var |-> "u", sub |-> <<  >>],
                                                                   rhs |-> << "u", "-", "v" >>]>>]>>]>>,
                           unlabDo |-> <<[type    |-> "if", 
                                          test    |-> << "u", "<", "v" >>,
                                          then |-> <<[type |-> "assignment",
                                                      ass  |-> <<[lhs |-> [var |-> "u", sub |-> <<  >>],
                                                                  rhs |-> << "v" >>], 
                                                                 [lhs |-> [var |-> "v", sub |-> <<  >>],
                                                                  rhs |-> << "u" >>]>>]>>,
                                          else |-> <<>>]>>], 
                          [type |-> "assert", 
                           exp |-> << "v", "=", "GCD", "(", "u_ini", ",", "v_ini", ")" >>]>>]>>]
==========================
