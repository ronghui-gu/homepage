type operator = Add | Sub | Mul | Div

type expr =
    Binop of expr * operator * expr
  | Seq of expr * expr
  | Asn of string * expr
  | Var of string
  | Lit of int
