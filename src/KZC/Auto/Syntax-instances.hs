instance Located LocalDecl where
  locOf (LetLD _ _ _ l) = locOf l
  locOf (LetRefLD _ _ _ l) = locOf l
instance Located Exp where
  locOf (ConstE _ l) = locOf l
  locOf (VarE _ l) = locOf l
  locOf (UnopE _ _ l) = locOf l
  locOf (BinopE _ _ _ l) = locOf l
  locOf (IfE _ _ _ l) = locOf l
  locOf (LetE _ _ l) = locOf l
  locOf (CallE _ _ _ l) = locOf l
  locOf (DerefE _ l) = locOf l
  locOf (AssignE _ _ l) = locOf l
  locOf (WhileE _ _ l) = locOf l
  locOf (ForE _ _ _ _ _ _ l) = locOf l
  locOf (ArrayE _ l) = locOf l
  locOf (IdxE _ _ _ l) = locOf l
  locOf (StructE _ _ l) = locOf l
  locOf (ProjE _ _ l) = locOf l
  locOf (PrintE _ _ l) = locOf l
  locOf (ErrorE _ _ l) = locOf l
  locOf (ReturnE _ _ l) = locOf l
  locOf (BindE _ _ _ l) = locOf l
