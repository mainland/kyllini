instance Located Var where
  locOf (Var l) = locOf l
instance Located Struct where
  locOf (Struct l) = locOf l
instance Located Field where
  locOf (Field l) = locOf l
instance Located Exp where
  locOf (ConstE _ l) = locOf l
  locOf (VarE _ l) = locOf l
  locOf (UnopE _ _ l) = locOf l
  locOf (BinopE _ _ _ l) = locOf l
  locOf (IfE _ _ _ l) = locOf l
  locOf (LetE _ _ _ _ l) = locOf l
  locOf (LetRefE _ _ _ _ l) = locOf l
  locOf (LetDeclE _ _ l) = locOf l
  locOf (CallE _ _ l) = locOf l
  locOf (AssignE _ _ l) = locOf l
  locOf (WhileE _ _ l) = locOf l
  locOf (UntilE _ _ l) = locOf l
  locOf (TimesE _ _ _ l) = locOf l
  locOf (ForE _ _ _ _ _ _ l) = locOf l
  locOf (ArrayE _ l) = locOf l
  locOf (IdxE _ _ _ l) = locOf l
  locOf (StructE _ _ l) = locOf l
  locOf (ProjE _ _ l) = locOf l
  locOf (PrintE _ _ l) = locOf l
  locOf (ErrorE _ l) = locOf l
  locOf (ReturnE _ _ l) = locOf l
  locOf (TakeE l) = locOf l
  locOf (TakesE _ l) = locOf l
  locOf (EmitE _ l) = locOf l
  locOf (EmitsE _ l) = locOf l
  locOf (RepeatE _ _ l) = locOf l
  locOf (ParE _ _ _ l) = locOf l
  locOf (ReadE _ l) = locOf l
  locOf (WriteE _ l) = locOf l
  locOf (StandaloneE _ l) = locOf l
  locOf (MapE _ _ _ l) = locOf l
  locOf (FilterE _ _ l) = locOf l
  locOf (StmE _ l) = locOf l
instance Located VarBind where
  locOf (VarBind _ _ _) = NoLoc
instance Located Decl where
  locOf (LetD _ _ _ l) = locOf l
  locOf (LetRefD _ _ _ l) = locOf l
  locOf (LetFunD _ _ _ _ l) = locOf l
  locOf (LetFunExternalD _ _ _ _ l) = locOf l
  locOf (LetStructD _ l) = locOf l
  locOf (LetCompD _ _ _ _ l) = locOf l
  locOf (LetFunCompD _ _ _ _ _ l) = locOf l
instance Located Stm where
  locOf (LetS _ l) = locOf l
  locOf (BindS _ _ _ l) = locOf l
  locOf (ExpS _ l) = locOf l
instance Located StructDef where
  locOf (StructDef _ _ l) = locOf l
instance Located Type where
  locOf (UnitT l) = locOf l
  locOf (BoolT l) = locOf l
  locOf (FixT _ l) = locOf l
  locOf (FloatT _ l) = locOf l
  locOf (ArrT _ _ l) = locOf l
  locOf (StructT _ l) = locOf l
  locOf (C _ l) = locOf l
  locOf (T l) = locOf l
  locOf (ST _ _ _ l) = locOf l
