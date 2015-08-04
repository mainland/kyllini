instance Located Var where
  locOf (Var l) = locOf l
instance Located Field where
  locOf (Field l) = locOf l
instance Located Struct where
  locOf (Struct l) = locOf l
instance Located TyVar where
  locOf (TyVar l) = locOf l
instance Located IVar where
  locOf (IVar l) = locOf l
instance Located Exp where
  locOf (ConstE _ l) = locOf l
  locOf (VarE _ l) = locOf l
  locOf (UnopE _ _ l) = locOf l
  locOf (BinopE _ _ _ l) = locOf l
  locOf (IfE _ _ _ l) = locOf l
  locOf (LetE _ _ _ _ l) = locOf l
  locOf (LetFunE _ _ _ _ _ _ l) = locOf l
  locOf (CallE _ _ _ l) = locOf l
  locOf (DerefE _ l) = locOf l
  locOf (AssignE _ _ l) = locOf l
  locOf (WhileE _ _ l) = locOf l
  locOf (UntilE _ _ l) = locOf l
  locOf (ForE _ _ _ _ l) = locOf l
  locOf (ArrayE _ l) = locOf l
  locOf (IdxE _ _ _ l) = locOf l
  locOf (LetStruct _ _ l) = locOf l
  locOf (ProjE _ _ l) = locOf l
  locOf (PrintE _ _ l) = locOf l
  locOf (ErrorE _ l) = locOf l
  locOf (ReturnE _ l) = locOf l
  locOf (BindE _ _ _ l) = locOf l
  locOf (TakeE l) = locOf l
  locOf (TakesE _ l) = locOf l
  locOf (EmitE _ l) = locOf l
  locOf (EmitsE _ l) = locOf l
  locOf (RepeatE _ l) = locOf l
  locOf (ArrE _ _ l) = locOf l
instance Located Type where
  locOf (UnitT l) = locOf l
  locOf (BoolT l) = locOf l
  locOf (BitT l) = locOf l
  locOf (IntT _ l) = locOf l
  locOf (FloatT _ l) = locOf l
  locOf (ComplexT _ l) = locOf l
  locOf (StringT l) = locOf l
  locOf (ArrT _ _ l) = locOf l
  locOf (StructT _ l) = locOf l
  locOf (ST _ _ _ _ _ l) = locOf l
  locOf (RefT _ l) = locOf l
  locOf (FunT _ _ _ l) = locOf l
  locOf (TyVarT _ l) = locOf l
