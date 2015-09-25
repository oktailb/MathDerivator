(* Fichier de lexage *)
{
#open "parser";;
#open "float";;

exception Eof;;
}

rule Token = parse
	 [` ` `\t`]			{ Token lexbuf					}
	|[`\n` `\r`]			{ EOL 						}
	|"PI"				{ PI 						}
	|"e"				{ E 						}
	|[`a`-`z`]+			{ VAR(get_lexeme lexbuf)			}
	|[`0`-`9`]+`.`[`0`-`9`]+	{ REAL(float_of_string (get_lexeme lexbuf)) 	}
	|[`0`-`9`]+			{ INT(float_of_string (get_lexeme lexbuf)) 	}
	|`+`				{ PLUS 						}
	|`-`				{ MINUS 					}
	|`*`				{ TIMES 					}
	|`/`				{ DIV 						}
	|"cos("				{ COS 						}
	|"sin("				{ SIN 						}
	|"tan("				{ TAN 						}
	|"ln("				{ LOG 						}
	|`^`				{ POW 						}
	|`(`				{ LPAREN 					}
	|`)`				{ RPAREN 					}
	|eof				{ raise Eof 					}
;;

