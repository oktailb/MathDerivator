/* File parser.mly */
%{
#open "types";;
%}
%token <float> REAL INT
%token <string> VAR
%token PLUS MINUS
%token TIMES DIV POW
%token LPAREN RPAREN
%token LOG TAN SIN COS
%token EOL
%token PI E
%left PLUS MINUS
%left TIMES DIV
%left POW
%right LPAREN COS SIN TAN LOG
%nonassoc UMINUS
%start Main
%type < 'a types__equation > Main
%%
Main:
	Expr EOL	{$1}
;
Expr:
	VAR				/* Ajouter la variable a la liste 	*/ 	{ Var($1)		}
	|PI				/* Constante Pi 			*/	{ Val(3.1415926535898)	}
	|E				/* Constante e 				*/	{ Val(2.718281828459)	}
	|REAL				/* Symbole terminal : nombre reel 	*/ 	{ Val($1)		}
	|INT				/* Symbole terminal : nombre entier 	*/ 	{ Val($1)		}
	|LPAREN Expr RPAREN		/* Les parentheses 			*/	{ Fun("(",$2,")")	}
	|COS Expr RPAREN		/* Expression Cosinus 			*/	{ Fun("cos(",$2,")")	}
	|SIN Expr RPAREN		/* Expression Sinus 			*/	{ Fun("sin(",$2,")")	}
	|TAN Expr RPAREN		/* Expression Tangente 			*/	{ Fun("tan(",$2,")")	}
	|LOG Expr RPAREN		/* Expression Logarithme base 10	*/ 	{ Fun("ln(",$2,")")	} 
	|Expr POW Expr			/* Expression Puissance 		*/	{ Op("^",$1,$3)		}
	|Expr PLUS Expr			/* Operateur + 				*/	{ Op("+",$1,$3)		}
	|Expr MINUS Expr		/* Operateur - 				*/	{ Op("-",$1,$3)		}
	|Expr TIMES Expr		/* Operateur * 				*/	{ Op("*",$1,$3)		}
	|Expr DIV Expr			/* Operateur / 				*/	{ Op("/",$1,$3)		}
	|MINUS Expr %prec UMINUS	/* Nombre negatif 			*/	{ UOp("-",$2)	}
;
%%
