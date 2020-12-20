src/Utils/Ensembles_Ext.vo src/Utils/Ensembles_Ext.glob src/Utils/Ensembles_Ext.v.beautified src/Utils/Ensembles_Ext.required_vo: src/Utils/Ensembles_Ext.v 
src/Utils/Ensembles_Ext.vio: src/Utils/Ensembles_Ext.v 
src/Utils/Ensembles_Ext.vos src/Utils/Ensembles_Ext.vok src/Utils/Ensembles_Ext.required_vos: src/Utils/Ensembles_Ext.v 
src/Utils/extralibrary.vo src/Utils/extralibrary.glob src/Utils/extralibrary.v.beautified src/Utils/extralibrary.required_vo: src/Utils/extralibrary.v 
src/Utils/extralibrary.vio: src/Utils/extralibrary.v 
src/Utils/extralibrary.vos src/Utils/extralibrary.vok src/Utils/extralibrary.required_vos: src/Utils/extralibrary.v 
src/Utils/Lattice.vo src/Utils/Lattice.glob src/Utils/Lattice.v.beautified src/Utils/Lattice.required_vo: src/Utils/Lattice.v 
src/Utils/Lattice.vio: src/Utils/Lattice.v 
src/Utils/Lattice.vos src/Utils/Lattice.vok src/Utils/Lattice.required_vos: src/Utils/Lattice.v 
src/Utils/stdpp_ext.vo src/Utils/stdpp_ext.glob src/Utils/stdpp_ext.v.beautified src/Utils/stdpp_ext.required_vo: src/Utils/stdpp_ext.v 
src/Utils/stdpp_ext.vio: src/Utils/stdpp_ext.v 
src/Utils/stdpp_ext.vos src/Utils/stdpp_ext.vok src/Utils/stdpp_ext.required_vos: src/Utils/stdpp_ext.v 
src/Syntax.vo src/Syntax.glob src/Syntax.v.beautified src/Syntax.required_vo: src/Syntax.v src/Utils/extralibrary.vo src/Utils/stdpp_ext.vo
src/Syntax.vio: src/Syntax.v src/Utils/extralibrary.vio src/Utils/stdpp_ext.vio
src/Syntax.vos src/Syntax.vok src/Syntax.required_vos: src/Syntax.v src/Utils/extralibrary.vos src/Utils/stdpp_ext.vos
src/Semantics.vo src/Semantics.glob src/Semantics.v.beautified src/Semantics.required_vo: src/Semantics.v src/Utils/Lattice.vo src/Utils/Ensembles_Ext.vo src/Utils/stdpp_ext.vo src/Utils/extralibrary.vo src/Syntax.vo
src/Semantics.vio: src/Semantics.v src/Utils/Lattice.vio src/Utils/Ensembles_Ext.vio src/Utils/stdpp_ext.vio src/Utils/extralibrary.vio src/Syntax.vio
src/Semantics.vos src/Semantics.vok src/Semantics.required_vos: src/Semantics.v src/Utils/Lattice.vos src/Utils/Ensembles_Ext.vos src/Utils/stdpp_ext.vos src/Utils/extralibrary.vos src/Syntax.vos
src/ProofSystem.vo src/ProofSystem.glob src/ProofSystem.v.beautified src/ProofSystem.required_vo: src/ProofSystem.v src/Utils/Ensembles_Ext.vo src/Syntax.vo src/Semantics.vo src/Helpers/monotonic.vo
src/ProofSystem.vio: src/ProofSystem.v src/Utils/Ensembles_Ext.vio src/Syntax.vio src/Semantics.vio src/Helpers/monotonic.vio
src/ProofSystem.vos src/ProofSystem.vok src/ProofSystem.required_vos: src/ProofSystem.v src/Utils/Ensembles_Ext.vos src/Syntax.vos src/Semantics.vos src/Helpers/monotonic.vos
src/SignatureHelper.vo src/SignatureHelper.glob src/SignatureHelper.v.beautified src/SignatureHelper.required_vo: src/SignatureHelper.v src/Syntax.vo src/Utils/extralibrary.vo
src/SignatureHelper.vio: src/SignatureHelper.v src/Syntax.vio src/Utils/extralibrary.vio
src/SignatureHelper.vos src/SignatureHelper.vok src/SignatureHelper.required_vos: src/SignatureHelper.v src/Syntax.vos src/Utils/extralibrary.vos
src/Logic.vo src/Logic.glob src/Logic.v.beautified src/Logic.required_vo: src/Logic.v src/Syntax.vo src/Semantics.vo src/ProofSystem.vo src/SignatureHelper.vo
src/Logic.vio: src/Logic.v src/Syntax.vio src/Semantics.vio src/ProofSystem.vio src/SignatureHelper.vio
src/Logic.vos src/Logic.vok src/Logic.required_vos: src/Logic.v src/Syntax.vos src/Semantics.vos src/ProofSystem.vos src/SignatureHelper.vos
src/Helpers/monotonic.vo src/Helpers/monotonic.glob src/Helpers/monotonic.v.beautified src/Helpers/monotonic.required_vo: src/Helpers/monotonic.v src/Utils/Lattice.vo src/Syntax.vo src/Semantics.vo
src/Helpers/monotonic.vio: src/Helpers/monotonic.v src/Utils/Lattice.vio src/Syntax.vio src/Semantics.vio
src/Helpers/monotonic.vos src/Helpers/monotonic.vok src/Helpers/monotonic.required_vos: src/Helpers/monotonic.v src/Utils/Lattice.vos src/Syntax.vos src/Semantics.vos
src/Helpers/FOL_helpers.vo src/Helpers/FOL_helpers.glob src/Helpers/FOL_helpers.v.beautified src/Helpers/FOL_helpers.required_vo: src/Helpers/FOL_helpers.v src/Syntax.vo src/Semantics.vo src/ProofSystem.vo
src/Helpers/FOL_helpers.vio: src/Helpers/FOL_helpers.v src/Syntax.vio src/Semantics.vio src/ProofSystem.vio
src/Helpers/FOL_helpers.vos src/Helpers/FOL_helpers.vok src/Helpers/FOL_helpers.required_vos: src/Helpers/FOL_helpers.v src/Syntax.vos src/Semantics.vos src/ProofSystem.vos
src/Theories/Definedness.vo src/Theories/Definedness.glob src/Theories/Definedness.v.beautified src/Theories/Definedness.required_vo: src/Theories/Definedness.v src/Syntax.vo src/Semantics.vo src/Utils/Ensembles_Ext.vo
src/Theories/Definedness.vio: src/Theories/Definedness.v src/Syntax.vio src/Semantics.vio src/Utils/Ensembles_Ext.vio
src/Theories/Definedness.vos src/Theories/Definedness.vok src/Theories/Definedness.required_vos: src/Theories/Definedness.v src/Syntax.vos src/Semantics.vos src/Utils/Ensembles_Ext.vos
src/Theories/Sorts.vo src/Theories/Sorts.glob src/Theories/Sorts.v.beautified src/Theories/Sorts.required_vo: src/Theories/Sorts.v src/Syntax.vo src/Theories/Definedness.vo
src/Theories/Sorts.vio: src/Theories/Sorts.v src/Syntax.vio src/Theories/Definedness.vio
src/Theories/Sorts.vos src/Theories/Sorts.vok src/Theories/Sorts.required_vos: src/Theories/Sorts.v src/Syntax.vos src/Theories/Definedness.vos
src/Tests/TEST_LocallyNameless.vo src/Tests/TEST_LocallyNameless.glob src/Tests/TEST_LocallyNameless.v.beautified src/Tests/TEST_LocallyNameless.required_vo: src/Tests/TEST_LocallyNameless.v src/Syntax.vo src/Semantics.vo src/SignatureHelper.vo src/Theories/Definedness.vo src/Theories/Sorts.vo src/Utils/Ensembles_Ext.vo
src/Tests/TEST_LocallyNameless.vio: src/Tests/TEST_LocallyNameless.v src/Syntax.vio src/Semantics.vio src/SignatureHelper.vio src/Theories/Definedness.vio src/Theories/Sorts.vio src/Utils/Ensembles_Ext.vio
src/Tests/TEST_LocallyNameless.vos src/Tests/TEST_LocallyNameless.vok src/Tests/TEST_LocallyNameless.required_vos: src/Tests/TEST_LocallyNameless.v src/Syntax.vos src/Semantics.vos src/SignatureHelper.vos src/Theories/Definedness.vos src/Theories/Sorts.vos src/Utils/Ensembles_Ext.vos
