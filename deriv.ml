(* File deriv.ml *)

#open "types";;

let rec puiss n x = if n=0.0 then 1.0
else
  let p = (puiss (n /. 2.0) x) in
  if (int_of_float(n) mod 2)=0 then
    p*.p
  else
    p*.p*.x;;

let rec print_equation = fun
	 (Val(x)) 	-> print_float x
	|(Var(s))	-> print_string s
	|(Fun(s1,e,s2))	-> print_string s1;print_equation e;print_string s2
	|(UOp(s,e))	-> print_string s;print_equation e
	|(Op(s,e1,e2))	-> print_equation e1;print_string s;print_equation e2
;;

let rec derive = fun
	 (Val(x)) (Var(s))	-> (Val(0.0))
	|(Var(s1)) (Var(s2))	-> if s1=s2 then (Val(1.0)) else (Val(0.0))
	|(Fun(s1,e,s2)) (Var(s))-> (match (s1,e,s2) with
					 ("(",_,_)		->	(Fun(s1,(derive e (Var(s))),s2))
					|("sin(",_,_)		->	Fun("cos(",e,")")
					|("cos(",_,_)		->	Fun("(",(UOp("-",(Fun("sin(",e,")")))),")")
					|("tan(",_,_)		->	derive (Op("/",(Fun("sin(",e,")")),(Fun("cos(",e,")")))) (Var(s))
					|("ln(",_,_)		->	Op("/",(Fun("(",(derive (e) (Var(s))),")")),e)
					|_			->	failwith "derive::Fonction inconnue ou non implementee !"
					)
	|(Op(s,e1,e2)) (Var(s2))-> (match (s,e1,e2) with
					 ("^",(Val(x)),_)	->	Op("*",(Op(s,e1,e2)),(derive e2 (Var(s2))))
					|("^",_,_)		->	Op("*",Op("*",(e2),(Op("^",e1,Op("-",e2,Val(1.0))))),(derive e1 (Var(s2))))
					|("+",_,_)		->	Op("+",(derive e1 (Var(s))),(derive e2 (Var(s2))))
					|("-",_,_)		->	Op("-",(derive e1 (Var(s))),(derive e2 (Var(s2))))
					|("*",_,_)		->	Op("+",Op("*",(e1),(derive e2 (Var(s2)))),Op("*",(derive e1 (Var(s2))),(e2)))
					|("/",_,_)		->	Op("/",Op("-",Op("*",(derive e1 (Var(s2))),e2),(Op("*",e1,(derive e2 (Var(s2)))))),Op("^",e2,(Val(2.0))))
					|_			->	failwith "derive::opérateur inconnu"
					)
	|(UOp(s,e)) (Var(s2))	-> (UOp(s,(derive e (Var(s2)))))
	|_ _			-> failwith "derive::arbre syntaxique corrompu"
;;

let rec
 add = fun
	 (Val(0.0)) (Var(x))		-> (Var(x))
	|(Val(0.0)) (Fun(s1,e,s2))	-> (Fun(s1,e,s2))
	|(Val(0.0)) (Op(s,e1,e2))	-> (Op(s,e1,e2))
	|(Val(0.0)) (UOp(s,e))		-> (UOp(s,e))
	|(Var(x)) (Val(0.0))		-> (Var(x))
	|(Fun(s1,e,s2)) (Val(0.0))	-> (Fun(s1,e,s2))
	|(Op(s,e1,e2)) (Val(0.0))	-> (Op(s,e1,e2))
	|(UOp(s,e)) (Val(0.0))		-> (UOp(s,e))
	|(Val(x)) (Val(y))		-> (Val(x+.y))
	|(Val(x)) (Var(s))		-> (Op("+",(Val(x)),Var(s)))
	|(Val(x)) (Op(s,e1,e2))		-> (Op("+",(Val(x)),(simpl_equation((Op(s,e1,e2))))))
	|(Val(x)) (UOp(s,e))		-> (Op("-",(Val(x)),simpl_equation e))
	|(Val(x)) (Fun(s1,e,s2))	-> (Op("+",(Val(x)),simpl_equation (Fun(s1,e,s2))))
	|(Var(s)) (Val(x))		-> (Op("+",(Val(x)),Var(s)))
	|(Var(s)) (Fun(s1,e,s2))	-> (Op("+",(Var(s)),simpl_equation (Fun(s1,e,s2))))
	|(Var(s)) (Op(s1,e1,e2))	-> (Op("+",(Var(s)),simpl_equation (Op(s1,e1,e2))))
	|(Var(s)) (UOp(s2,e))		-> (Op("-",(Var(s)),e))
	|(Var(s1)) (Var(s2))		-> if s1=s2 then (Op("*",(Val(2.0)),(Var(s1)))) else Op("+",(Var(s1)),(Var(s2)))
	|(Fun(s1,e1,s2)) (Fun(s3,e2,s4))-> if s1=s3 then if e1=e2 then (Op("*",(Val(2.0)),(Fun(s1,e1,s2)))) else (Op("+",(simpl_equation(Fun(s1,e1,s2))),(simpl_equation(Fun(s3,e2,s4))))) else (Op("+",(simpl_equation(Fun(s1,e1,s2))),(simpl_equation(Fun(s3,e2,s4)))))
	|(Fun(s1,e,s2)) (Val(x))	-> (Op("+",(simpl_equation(Fun(s1,e,s2))),(Val(x))))
	|(Fun(s1,e,s2)) (Var(s))	-> (Op("+",(simpl_equation(Fun(s1,e,s2))),(Var(s))))
	|(Fun(s1,e1,s2)) (Op(s3,e2,e3))	-> (Op("+",(simpl_equation(Fun(s1,e1,s2))),simpl_equation(Op(s3,e2,e3))))
	|(Fun(s1,e1,s2)) (UOp(s3,e2))	-> (Op("-",(simpl_equation(Fun(s1,e1,s2))),simpl_equation(e2)))
	|(Op(s,e1,e2)) (Val(x))		-> (Op("+",(Val(x)),(simpl_equation((Op(s,e1,e2))))))
	|(Op(s1,e1,e2)) (Var(s2))	-> (Op("+",(Var(s2)),(simpl_equation((Op(s1,e1,e2))))))
	|(Op(s1,e1,e2)) (Fun(s2,e3,s3))	-> (Op("+",(simpl_equation(Fun(s2,e3,s3))),(simpl_equation(Op(s1,e1,e2)))))
	|(Op(s1,e1,e2)) (Op(s2,e3,e4))	-> (Op("+",(simpl_equation(Op(s1,e1,e2))),(simpl_equation(Op(s2,e3,e4)))))
	|(Op(s1,e1,e2)) (UOp(s2,e3))	-> (Op("-",(simpl_equation(Op(s1,e1,e2))),(simpl_equation(e3))))
	|(UOp(s1,e1)) (UOp(s2,e2))	-> (UOp("-",(simpl_equation(Fun("(",(Op("+",e1,e2)),")")))))
	|(UOp(s,e)) (Val(x))		-> (Op("-",(Val(x)),(simpl_equation e)))
	|(UOp(s,e)) (Var(s2))		-> (Op("-",(Var(s2)),(simpl_equation e)))
	|(UOp(s,e)) (Fun(s2,e2,s3))	-> (Op("-",((simpl_equation (Fun(s2,e2,s3)))),(simpl_equation e)))
	|(UOp(s,e)) (Op(e2,s2,e3))	-> (Op("-",(simpl_equation (Op(e2,s2,e3))),(simpl_equation e)))
and

 sub = fun
	 (Var(x)) (Val(0.0))		-> (Var(x))
	|(Fun(s1,e,s2)) (Val(0.0))	-> (Fun(s1,e,s2))
	|(Op(s,e1,e2)) (Val(0.0))	-> (Op(s,e1,e2))
	|(UOp(s,e)) (Val(0.0))		-> (UOp(s,e))
	|(Val(0.0)) (Var(x))		-> (Var(x))
	|(Val(0.0)) (Fun(s1,e,s2))	-> (Fun(s1,e,s2))
	|(Val(0.0)) (Op(s,e1,e2))	-> (Op(s,e1,e2))
	|(Val(0.0)) (UOp(s,e))		-> (UOp(s,e))
	|(Val(x)) (Val(y))		-> (Val(x-.y))
	|(Val(x)) (Var(s))		-> (Op("-",(Val(x)),Var(s)))
	|(Val(x)) (Op(s,e1,e2))		-> (Op("-",(Val(x)),(simpl_equation((Op(s,e1,e2))))))
	|(Val(x)) (UOp(s,e))		-> (Op("+",(Val(x)),simpl_equation e))
	|(Val(x)) (Fun(s1,e,s2))	-> (Op("-",(Val(x)),simpl_equation (Fun(s1,e,s2))))
	|(Var(s)) (Val(x))		-> (Op("-",(Var(s)),Val(x)))
	|(Var(s)) (Fun(s1,e,s2))	-> (Op("-",(Var(s)),simpl_equation (Fun(s1,e,s2))))
	|(Var(s)) (Op(s1,e1,e2))	-> (Op("-",(Var(s)),simpl_equation (Op(s1,e1,e2))))
	|(Var(s)) (UOp(s2,e))		-> (Op("+",(Var(s)),e))
	|(Var(s1)) (Var(s2))		-> if s1=s2 then (Val(0.0)) else Op("-",(Var(s1)),(Var(s2)))
	|(Fun(s1,e1,s2)) (Fun(s3,e2,s4))-> (Op("-",(simpl_equation(Fun(s1,e1,s2))),(simpl_equation(Fun(s3,e2,s4)))))
	|(Fun(s1,e,s2)) (Val(x))	-> (Op("-",(simpl_equation(Fun(s1,e,s2))),(Val(x))))
	|(Fun(s1,e,s2)) (Var(s))	-> (Op("-",(simpl_equation(Fun(s1,e,s2))),(Var(s))))
	|(Fun(s1,e1,s2)) (Op(s3,e2,e3))	-> (Op("-",(simpl_equation(Fun(s1,e1,s2))),simpl_equation(Op(s3,e2,e3))))
	|(Fun(s1,e1,s2)) (UOp(s3,e2))	-> (Op("+",(simpl_equation(Fun(s1,e1,s2))),simpl_equation(e2)))
	|(Op(s,e1,e2)) (Val(x))		-> (Op("-",(Val(x)),(simpl_equation((Op(s,e1,e2))))))
	|(Op(s1,e1,e2)) (Var(s2))	-> (Op("-",(Var(s2)),(simpl_equation((Op(s1,e1,e2))))))
	|(Op(s1,e1,e2)) (Fun(s2,e3,s3))	-> (Op("-",(simpl_equation(Fun(s2,e3,s3))),(simpl_equation(Op(s1,e1,e2)))))
	|(Op(s1,e1,e2)) (Op(s2,e3,e4))	-> (Op("-",(simpl_equation(Op(s1,e1,e2))),(simpl_equation(Op(s2,e3,e4)))))
	|(Op(s1,e1,e2)) (UOp(s2,e3))	-> (Op("+",(simpl_equation(Op(s1,e1,e2))),(simpl_equation(e3))))
	|(UOp(s1,e1)) (UOp(s2,e2))	-> (UOp("-",(simpl_equation(Fun("(",(Op("-",e1,e2)),")")))))
	|(UOp(s,e)) (Val(x))		-> (Op("-",(simpl_equation (UOp(s,e))),(Val(x))))
	|(UOp(s,e)) (Var(s2))		-> (Op("-",(simpl_equation (UOp(s,e))),(Var(s2))))
	|(UOp(s,e)) (Fun(s2,e2,s3))	-> (Op("-",(simpl_equation(UOp(s,e))),((simpl_equation (Fun(s2,e2,s3))))))
	|(UOp(s,e)) (Op(e2,s2,e3))	-> (Op("-",(simpl_equation(UOp(s,e))),((simpl_equation (Op(e2,s2,e3))))))
and

 mul = fun
	 (Fun("ln(",e1,")")) (Fun("ln(",e2,")"))	-> (Fun("ln(",(Op("+",e1,e2)),")"))
	|(Var(x)) (Val(1.0))		-> (Var(x))
	|(Fun(s1,e,s2)) (Val(1.0))	-> (Fun(s1,e,s2))
	|(Op(s,e1,e2)) (Val(1.0))	-> (Op(s,e1,e2))
	|(UOp(s,e)) (Val(1.0))		-> (UOp(s,e))
	|(Val(1.0)) (Var(x))		-> (Var(x))
	|(Val(1.0)) (Fun(s1,e,s2))	-> (Fun(s1,e,s2))
	|(Val(1.0)) (Op(s,e1,e2))	-> (Op(s,e1,e2))
	|(Val(1.0)) (UOp(s,e))		-> (UOp(s,e))
	|(Var(x)) (Val(0.0))		-> (Val(0.0))
	|(Fun(s1,e,s2)) (Val(0.0))	-> (Val(0.0))
	|(Op(s,e1,e2)) (Val(0.0))	-> (Val(0.0))
	|(UOp(s,e)) (Val(0.0))		-> (Val(0.0))
	|(Val(0.0)) (Var(x))		-> (Val(0.0))
	|(Val(0.0)) (Fun(s1,e,s2))	-> (Val(0.0))
	|(Val(0.0)) (Op(s,e1,e2))	-> (Val(0.0))
	|(Val(0.0)) (UOp(s,e))		-> (Val(0.0))
	|(Val(x)) (Val(y))		-> (Val(x*.y))
	|(Val(x)) (Var(s))		-> (Op("*",(Val(x)),Var(s)))
	|(Val(x)) (Op(s,e1,e2))		-> (Op("*",(Val(x)),(simpl_equation((Op(s,e1,e2))))))
	|(Val(x)) (UOp(s,e))		-> (UOp("-",(Op("*",(Val(x)),simpl_equation e))))
	|(Val(x)) (Fun(s1,e,s2))	-> (Op("*",(Val(x)),simpl_equation (Fun(s1,e,s2))))
	|(Var(s)) (Val(x))		-> (Op("*",(Val(x)),Var(s)))
	|(Var(s)) (Fun(s1,e,s2))	-> (Op("*",(Var(s)),simpl_equation (Fun(s1,e,s2))))
	|(Var(s)) (Op(s1,e1,e2))	-> (Op("*",(Var(s)),simpl_equation (Op(s1,e1,e2))))
	|(Var(s)) (UOp(s2,e))		-> (UOp("-",(Op("*",(Var(s)),e))))
	|(Var(s1)) (Var(s2))		-> if s1=s2 then (Op("^",(Var(s1)),(Val(2.0)))) else Op("*",(Var(s1)),(Var(s2)))
	|(Fun(s1,e1,s2)) (Fun(s3,e2,s4))-> if(s1=s3) & (e1=e2) then (Op("^",(Fun(s1,e1,s2)),(Val(2.0)))) else (Op("*",(simpl_equation(Fun(s1,e1,s2))),(simpl_equation(Fun(s3,e2,s4)))))
	|(Fun(s1,e,s2)) (Val(x))	-> (Op("*",(simpl_equation(Fun(s1,e,s2))),(Val(x))))
	|(Fun(s1,e,s2)) (Var(s))	-> (Op("*",(simpl_equation(Fun(s1,e,s2))),(Var(s))))
	|(Fun(s1,e1,s2)) (Op(s3,e2,e3))	-> (Op("*",(simpl_equation(Fun(s1,e1,s2))),simpl_equation(Op(s3,e2,e3))))
	|(Fun(s1,e1,s2)) (UOp(s3,e2))	-> (UOp("-",(Op("*",(simpl_equation(Fun(s1,e1,s2))),simpl_equation(e2)))))
	|(Op(s,e1,e2)) (Val(x))		-> (Op("*",(Val(x)),(simpl_equation((Op(s,e1,e2))))))
	|(Op(s1,e1,e2)) (Var(s2))	-> (Op("*",(Var(s2)),(simpl_equation((Op(s1,e1,e2))))))
	|(Op(s1,e1,e2)) (Fun(s2,e3,s3))	-> (Op("*",(simpl_equation(Fun(s2,e3,s3))),(simpl_equation(Op(s1,e1,e2)))))
	|(Op(s1,e1,e2)) (Op(s2,e3,e4))	-> (Op("*",(simpl_equation(Op(s1,e1,e2))),(simpl_equation(Op(s2,e3,e4)))))
	|(Op(s1,e1,e2)) (UOp(s2,e3))	-> (UOp("-",(Op("*",(simpl_equation(Op(s1,e1,e2))),(simpl_equation(e3))))))
	|(UOp(s1,e1)) (UOp(s2,e2))	-> (Op("*",(simpl_equation e1),(simpl_equation e2)))
	|(UOp(s,e)) (Val(x))		-> (UOp("-",(Op("*",(simpl_equation (UOp(s,e))),(Val(x))))))
	|(UOp(s,e)) (Var(s2))		-> (UOp("-",Op("*",(simpl_equation e),(Var(s2)))))
	|(UOp(s,e)) (Fun(s2,e2,s3))	-> (UOp("-",(Op("*",(simpl_equation(e)),((simpl_equation (Fun(s2,e2,s3))))))))
	|(UOp(s,e)) (Op(e2,s2,e3))	-> (UOp("-",(Op("*",(simpl_equation(e)),((simpl_equation (Op(e2,s2,e3))))))))
and

 div = fun
	 (Fun("ln(",e1,")")) (Fun("ln(",e2,")"))	-> (Fun("ln(",(Op("-",e1,e2)),")"))
	|_ (Val(0.0))			-> failwith "div::fatal error : division by zero !"
	|(Var(x)) (Val(1.0))		-> (Var(x))
	|(Fun("sin(",e1,")")) (Fun("cos(",e2,")"))	-> if e1=e2 then (Fun("tan(",e1,")")) else (Op("/",(Fun("sin(",(simpl_equation(e1)),")")),(Fun("cos(",(simpl_equation(e2)),")"))))
	|(Fun(s1,e,s2)) (Val(1.0))	-> (Fun(s1,e,s2))
	|(Op(s,e1,e2)) (Val(1.0))	-> (Op(s,e1,e2))
	|(UOp(s,e)) (Val(1.0))		-> (UOp(s,e))
	|(Val(0.0)) (Var(x))		-> (Val(0.0))
	|(Val(0.0)) (Fun(s1,e,s2))	-> (Val(0.0))
	|(Val(0.0)) (Op(s,e1,e2))	-> (Val(0.0))
	|(Val(0.0)) (UOp(s,e))		-> (Val(0.0))
	|(Val(x)) (Val(y))		-> (Val(x/.y))
	|(Val(x)) (Var(s))		-> (Op("/",(Val(x)),Var(s)))
	|(Val(x)) (Op(s,e1,e2))		-> (Op("/",(Val(x)),(simpl_equation((Op(s,e1,e2))))))
	|(Val(x)) (UOp(s,e))		-> (UOp("-",(Op("/",(Val(x)),simpl_equation e))))
	|(Val(x)) (Fun(s1,e,s2))	-> (Op("/",(Val(x)),simpl_equation (Fun(s1,e,s2))))
	|(Var(s)) (Val(x))		-> (Op("/",(Var(s)),Val(x)))
	|(Var(s)) (Fun(s1,e,s2))	-> (Op("/",(Var(s)),simpl_equation (Fun(s1,e,s2))))
	|(Var(s)) (Op(s1,e1,e2))	-> (Op("/",(Var(s)),simpl_equation (Op(s1,e1,e2))))
	|(Var(s)) (UOp(s2,e))		-> (UOp("-",(Op("/",(Var(s)),e))))
	|(Var(s1)) (Var(s2))		-> if s1=s2 then (Val(1.0)) else Op("/",(Var(s1)),(Var(s2)))
	|(Fun(s1,e1,s2)) (Fun(s3,e2,s4))-> (Op("/",(simpl_equation(Fun(s1,e1,s2))),(simpl_equation(Fun(s3,e2,s4)))))
	|(Fun(s1,e,s2)) (Val(x))	-> (Op("/",(simpl_equation(Fun(s1,e,s2))),(Val(x))))
	|(Fun(s1,e,s2)) (Var(s))	-> (Op("/",(simpl_equation(Fun(s1,e,s2))),(Var(s))))
	|(Fun(s1,e1,s2)) (Op(s3,e2,e3))	-> (Op("/",(simpl_equation(Fun(s1,e1,s2))),simpl_equation(Op(s3,e2,e3))))
	|(Fun(s1,e1,s2)) (UOp(s3,e2))	-> (UOp("-",(Op("/",(simpl_equation(Fun(s1,e1,s2))),simpl_equation(e2)))))
	|(Op(s,e1,e2)) (Val(x))		-> (Op("/",(simpl_equation((Op(s,e1,e2)))),(Val(x))))
	|(Op(s1,e1,e2)) (Var(s2))	-> (Op("/",(simpl_equation((Op(s1,e1,e2)))),(Var(s2))))
	|(Op(s1,e1,e2)) (Fun(s2,e3,s3))	-> (Op("/",(simpl_equation(Fun(s2,e3,s3))),(simpl_equation(Op(s1,e1,e2)))))
	|(Op(s1,e1,e2)) (Op(s2,e3,e4))	-> (Op("/",(simpl_equation(Op(s1,e1,e2))),(simpl_equation(Op(s2,e3,e4)))))
	|(Op(s1,e1,e2)) (UOp(s2,e3))	-> (UOp("-",(Op("/",(simpl_equation(Op(s1,e1,e2))),(simpl_equation(e3))))))
	|(UOp(s1,e1)) (UOp(s2,e2))	-> (Op("/",(simpl_equation e1),(simpl_equation e2)))
	|(UOp(s,e)) (Val(x))		-> (UOp("-",(Op("/",(simpl_equation e),(Val(x))))))
	|(UOp(s,e)) (Var(s2))		-> (UOp("-",Op("/",(simpl_equation e),(Var(s2)))))
	|(UOp(s,e)) (Fun(s2,e2,s3))	-> (UOp("-",(Op("/",(simpl_equation(e)),((simpl_equation (Fun(s2,e2,s3))))))))
	|(UOp(s,e)) (Op(e2,s2,e3))	-> (UOp("-",(Op("/",(simpl_equation(e)),((simpl_equation (Op(e2,s2,e3))))))))
and

 pow = fun
	 (Var(s)) (Val(1.0))		-> (Var(s))
	|(Val(x)) (Val(y))		-> (Val((puiss y x)))
	|(Val(x)) (Var(s))		-> (Op("^",(Val(x)),Var(s)))
	|(Val(x)) (Op(s,e1,e2))		-> (Op("^",(Val(x)),(simpl_equation((Op(s,e1,e2))))))
	|(Val(x)) (UOp(s,e))		-> (Op("^",(Val(x)),simpl_equation (UOp(s,e))))
	|(Val(x)) (Fun(s1,e,s2))	-> (Op("^",(Val(x)),simpl_equation (Fun(s1,e,s2))))
	|(Var(s)) (Val(x))		-> (Op("^",(Var(s)),Val(x)))
	|(Var(s)) (Fun(s1,e,s2))	-> (Op("^",(Var(s)),simpl_equation (Fun(s1,e,s2))))
	|(Var(s)) (Op(s1,e1,e2))	-> (Op("^",(Var(s)),simpl_equation (Op(s1,e1,e2))))
	|(Var(s)) (UOp(s2,e))		-> (Op("/",(Var(s)),(UOp(s,e))))
	|(Var(s1)) (Var(s2))		-> (Op("^",(Var(s1)),(Var(s2))))
	|(Fun(s1,e1,s2)) (Fun(s3,e2,s4))-> (Op("^",(simpl_equation(Fun(s1,e1,s2))),(simpl_equation(Fun(s3,e2,s4)))))
	|(Fun(s1,e,s2)) (Val(x))	-> (Op("^",(simpl_equation(Fun(s1,e,s2))),(Val(x))))
	|(Fun(s1,e,s2)) (Var(s))	-> (Op("^",(simpl_equation(Fun(s1,e,s2))),(Var(s))))
	|(Fun(s1,e1,s2)) (Op(s3,e2,e3))	-> (Op("^",(simpl_equation(Fun(s1,e1,s2))),simpl_equation(Op(s3,e2,e3))))
	|(Fun(s1,e1,s2)) (UOp(s3,e2))	-> (Op("^",(simpl_equation(Fun(s1,e1,s2))),simpl_equation((UOp(s3,e2)))))
	|(Op(s,e1,e2)) (Val(x))		-> (Op("^",(simpl_equation((Op(s,e1,e2)))),(Val(x))))
	|(Op(s1,e1,e2)) (Var(s2))	-> (Op("^",(simpl_equation((Op(s1,e1,e2)))),(Var(s2))))
	|(Op(s1,e1,e2)) (Fun(s2,e3,s3))	-> (Op("^",(simpl_equation(Fun(s2,e3,s3))),(simpl_equation(Op(s1,e1,e2)))))
	|(Op(s1,e1,e2)) (Op(s2,e3,e4))	-> (Op("^",(simpl_equation(Op(s1,e1,e2))),(simpl_equation(Op(s2,e3,e4)))))
	|(Op(s1,e1,e2)) (UOp(s2,e3))	-> (Op("^",(simpl_equation(Op(s1,e1,e2))),(simpl_equation((UOp(s2,e3))))))
	|(UOp(s1,e1)) (UOp(s2,e2))	-> (Op("^",(simpl_equation (UOp(s1,e1))),(simpl_equation (UOp(s2,e2)))))
	|(UOp(s,e)) (Val(x))		-> (Op("^",(simpl_equation (UOp(s,e))),(Val(x))))
	|(UOp(s,e)) (Var(s2))		-> (Op("^",(simpl_equation (UOp(s,e))),(Var(s2))))
	|(UOp(s,e)) (Fun(s2,e2,s3))	-> (Op("^",(simpl_equation (UOp(s,e))),(simpl_equation (Fun(s2,e2,s3)))))
	|(UOp(s,e)) (Op(e2,s2,e3))	-> (Op("^",(simpl_equation (UOp(s,e))),(simpl_equation (Op(e2,s2,e3)))))
and


 simpl_equation = fun
	 (Val(x))	-> (Val(x))
	|(Var(s))	-> (Var(s))
	|(Fun(s1,e,s2))	-> (match (s1,e,s2) with
				 ("(",_,_)		->	e
				 |("cos(",Val(x),_)	->	(Val(cos x))
				 |("sin(",Val(x),_)	->	(Val(sin x))
				 |("tan(",Val(x),_)	->	(Val(tan x))
				 |("ln(",Val(x),_)	->	(Val(log x))
				 |_			->	(Fun(s1,(simpl_equation e),s2))
				 )
	|(UOp(s,e))	-> (UOp("-",(simpl_equation e)))
	|(Op(s,e1,e2))  -> (match (s,e1,e2) with
				 ("+",_,_)	->	add (simpl_equation e1) (simpl_equation e2)
				|("-",_,_)	->	sub (simpl_equation e1) (simpl_equation e2)
				|("*",_,_)	->	mul (simpl_equation e1) (simpl_equation e2)
				|("/",_,_)	->	div (simpl_equation e1) (simpl_equation e2)
				|("^",_,_)	->	pow (simpl_equation e1) (simpl_equation e2)
				|_		->	failwith "calc_equation::Operateur inconnu ou non implemente !"
				)
;;

try
	let lexbuf = lexing__create_lexer_channel std_in in
	let result = parser__Main  lexer__Token lexbuf in
		print_string "Vous avez entre l'equation : ";
		print_equation result;
		print_newline();
		print_string "Autrement dit              : ";
		let nresult = simpl_equation result in
		print_equation nresult;
		print_newline();
		print_string "Selon quelle variable la deriver ? ";
		print_newline();
		let dvar = input_line std_in in
		print_string "Qui derivee donne          : ";
		let dresult = derive nresult (Var(dvar)) in
		print_equation dresult;
		print_newline();
		print_string "puis simplifiee donne      : ";
		let fresult = simpl_equation dresult in
		print_equation fresult;
		print_newline();
		flush std_out;
with Eof ->
	()
;;
