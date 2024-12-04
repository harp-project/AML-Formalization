Require Export MatchingLogic.Signature.

Definition StringMLVariables : MLVariables :=
  {| evar := string;
     svar := string;
     string2evar := @id string;
     string2svar := @id string;
  |}.
