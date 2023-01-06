Bits.vo Bits.glob Bits.v.beautified Bits.required_vo: Bits.v 
Bits.vio: Bits.v 
Bits.vos Bits.vok Bits.required_vos: Bits.v 
Util.vo Util.glob Util.v.beautified Util.required_vo: Util.v Bits.vo
Util.vio: Util.v Bits.vio
Util.vos Util.vok Util.required_vos: Util.v Bits.vos
GenericSyntax.vo GenericSyntax.glob GenericSyntax.v.beautified GenericSyntax.required_vo: GenericSyntax.v Bits.vo Util.vo
GenericSyntax.vio: GenericSyntax.v Bits.vio Util.vio
GenericSyntax.vos GenericSyntax.vok GenericSyntax.required_vos: GenericSyntax.v Bits.vos Util.vos
GenericSemantics.vo GenericSemantics.glob GenericSemantics.v.beautified GenericSemantics.required_vo: GenericSemantics.v Bits.vo Util.vo GenericSyntax.vo
GenericSemantics.vio: GenericSemantics.v Bits.vio Util.vio GenericSyntax.vio
GenericSemantics.vos GenericSemantics.vok GenericSemantics.required_vos: GenericSemantics.v Bits.vos Util.vos GenericSyntax.vos
X86Syntax.vo X86Syntax.glob X86Syntax.v.beautified X86Syntax.required_vo: X86Syntax.v Bits.vo Util.vo GenericSyntax.vo
X86Syntax.vio: X86Syntax.v Bits.vio Util.vio GenericSyntax.vio
X86Syntax.vos X86Syntax.vok X86Syntax.required_vos: X86Syntax.v Bits.vos Util.vos GenericSyntax.vos
X86Semantics.vo X86Semantics.glob X86Semantics.v.beautified X86Semantics.required_vo: X86Semantics.v Util.vo Bits.vo GenericSyntax.vo GenericSemantics.vo X86Syntax.vo
X86Semantics.vio: X86Semantics.v Util.vio Bits.vio GenericSyntax.vio GenericSemantics.vio X86Syntax.vio
X86Semantics.vos X86Semantics.vok X86Semantics.required_vos: X86Semantics.v Util.vos Bits.vos GenericSyntax.vos GenericSemantics.vos X86Syntax.vos
EarlyBirdSyntax.vo EarlyBirdSyntax.glob EarlyBirdSyntax.v.beautified EarlyBirdSyntax.required_vo: EarlyBirdSyntax.v Bits.vo Util.vo GenericSyntax.vo
EarlyBirdSyntax.vio: EarlyBirdSyntax.v Bits.vio Util.vio GenericSyntax.vio
EarlyBirdSyntax.vos EarlyBirdSyntax.vok EarlyBirdSyntax.required_vos: EarlyBirdSyntax.v Bits.vos Util.vos GenericSyntax.vos
EarlyBirdSemantics.vo EarlyBirdSemantics.glob EarlyBirdSemantics.v.beautified EarlyBirdSemantics.required_vo: EarlyBirdSemantics.v Util.vo Bits.vo GenericSyntax.vo GenericSemantics.vo EarlyBirdSyntax.vo
EarlyBirdSemantics.vio: EarlyBirdSemantics.v Util.vio Bits.vio GenericSyntax.vio GenericSemantics.vio EarlyBirdSyntax.vio
EarlyBirdSemantics.vos EarlyBirdSemantics.vok EarlyBirdSemantics.required_vos: EarlyBirdSemantics.v Util.vos Bits.vos GenericSyntax.vos GenericSemantics.vos EarlyBirdSyntax.vos
Reg2Var.vo Reg2Var.glob Reg2Var.v.beautified Reg2Var.required_vo: Reg2Var.v Bits.vo Util.vo GenericSyntax.vo GenericSemantics.vo EarlyBirdSyntax.vo X86Syntax.vo EarlyBirdSemantics.vo X86Semantics.vo
Reg2Var.vio: Reg2Var.v Bits.vio Util.vio GenericSyntax.vio GenericSemantics.vio EarlyBirdSyntax.vio X86Syntax.vio EarlyBirdSemantics.vio X86Semantics.vio
Reg2Var.vos Reg2Var.vok Reg2Var.required_vos: Reg2Var.v Bits.vos Util.vos GenericSyntax.vos GenericSemantics.vos EarlyBirdSyntax.vos X86Syntax.vos EarlyBirdSemantics.vos X86Semantics.vos
Extraction.vo Extraction.glob Extraction.v.beautified Extraction.required_vo: Extraction.v Reg2Var.vo
Extraction.vio: Extraction.v Reg2Var.vio
Extraction.vos Extraction.vok Extraction.required_vos: Extraction.v Reg2Var.vos
