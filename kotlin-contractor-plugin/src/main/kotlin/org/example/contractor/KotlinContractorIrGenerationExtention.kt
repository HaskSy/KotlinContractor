package org.example.contractor

import org.example.contractor.transformers.EchoTransformer
import org.example.contractor.transformers.RequiresTransformer
import org.jetbrains.kotlin.backend.common.extensions.IrGenerationExtension
import org.jetbrains.kotlin.backend.common.extensions.IrPluginContext
import org.jetbrains.kotlin.ir.declarations.IrModuleFragment
import org.jetbrains.kotlin.name.CallableId
import org.jetbrains.kotlin.name.ClassId
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.name.Name

class KotlinContractorIrGenerationExtention(
) : IrGenerationExtension {
    override fun generate(moduleFragment: IrModuleFragment, pluginContext: IrPluginContext) {

        val echoAnnotationFqName = FqName("org.example.contractor.Echo")
        val echoAnnotation = pluginContext.referenceClass(ClassId(
            echoAnnotationFqName.parent(),
            echoAnnotationFqName.shortName()
        ))!!

        val requiresAnnotationFqName = FqName("org.example.contractor.Requires")

        val typeAnyNullable = pluginContext.irBuiltIns.anyNType

        val funPrintln = pluginContext.referenceFunctions(
            CallableId(
            packageName = FqName("kotlin.io"),
            callableName = Name.identifier("println")
        )).single {
            val parameters = it.owner.valueParameters
            parameters.size == 1 && parameters[0].type == typeAnyNullable
        }

        moduleFragment.transform(EchoTransformer(pluginContext, echoAnnotation, funPrintln), null)
        moduleFragment.transform(RequiresTransformer(pluginContext, requiresAnnotationFqName, funPrintln), null)
    }
}
