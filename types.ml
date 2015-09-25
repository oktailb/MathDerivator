type 'a equation =
    |Val of float
    |Var of string
    |Fun of string*('a equation)*string
    |UOp of string*('a equation)
    |Op of string*('a equation)*('a equation)
;;
