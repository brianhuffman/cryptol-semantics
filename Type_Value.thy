theory Type_Value
imports
  Main
  "~~/src/HOL/Library/Extended_Nat"
begin

type_synonym field_name = string

datatype tvalue
  = TVBit
  | TVInteger
  | TVSeq nat tvalue
  | TVStream tvalue
  | TVTuple "tvalue list"
  | TVRecord "(field_name \<times> tvalue) list"
  | TVFun tvalue tvalue

primrec tvSeq :: "enat \<Rightarrow> tvalue \<Rightarrow> tvalue" where
  "tvSeq (enat n) = TVSeq n" |
  "tvSeq infinity = TVStream"

subsection {* Class instances *}

declare list.pred_mono [mono] (* Why is this not pre-declared? *)

inductive pFin :: "enat \<Rightarrow> bool" where
  "pFin (enat n)"

inductive pZero :: "tvalue \<Rightarrow> bool" where
  "pZero TVBit" |
  "pZero TVInteger" |
  "pZero t \<Longrightarrow> pZero (TVSeq n t)" |
  "pZero t \<Longrightarrow> pZero (TVStream t)" |
  "list_all pZero ts \<Longrightarrow> pZero (TVTuple ts)" |
  "list_all (\<lambda>(f,t). pZero t) fs \<Longrightarrow> pZero (TVRecord fs)" |
  "pZero b \<Longrightarrow> pZero (TVFun a b)"

inductive pLogic :: "tvalue \<Rightarrow> bool" where
  "pLogic TVBit" |
  "pLogic t \<Longrightarrow> pLogic (TVSeq n t)" |
  "pLogic t \<Longrightarrow> pLogic (TVStream t)" |
  "list_all pLogic ts \<Longrightarrow> pLogic (TVTuple ts)" |
  "list_all (\<lambda>(f,t). pLogic t) fs \<Longrightarrow> pLogic (TVRecord fs)" |
  "pLogic b \<Longrightarrow> pLogic (TVFun a b)"

inductive pArith :: "tvalue \<Rightarrow> bool" where
  "pArith (TVSeq n TVBit)" |
  "pArith t \<Longrightarrow> pArith (TVStream t)" |
  "list_all pArith ts \<Longrightarrow> pArith (TVTuple ts)" |
  "list_all (\<lambda>(f,t). pArith t) fs \<Longrightarrow> pArith (TVRecord fs)" |
  "pArith b \<Longrightarrow> pArith (TVFun a b)"

inductive pCmp :: "tvalue \<Rightarrow> bool" where
  "pCmp TVBit" |
  "pCmp TVInteger" |
  "pCmp t \<Longrightarrow> pCmp (TVSeq n t)" |
  "list_all pCmp ts \<Longrightarrow> pCmp (TVTuple ts)" |
  "list_all (\<lambda>(f,t). pCmp t) fs \<Longrightarrow> pCmp (TVRecord fs)"

inductive pSignedCmp :: "tvalue \<Rightarrow> bool" where
  "0 < n \<Longrightarrow> pSignedCmp (TVSeq n TVBit)" |
  "pSignedCmp t \<Longrightarrow> pSignedCmp (TVSeq n t)" |
  "list_all pSignedCmp ts \<Longrightarrow> pSignedCmp (TVTuple ts)" |
  "list_all (\<lambda>(f,t). pSignedCmp t) fs \<Longrightarrow> pSignedCmp (TVRecord fs)"

end
