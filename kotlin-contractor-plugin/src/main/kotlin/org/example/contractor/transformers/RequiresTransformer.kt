package org.example.contractor.transformers

import org.jetbrains.kotlin.backend.common.IrElementTransformerVoidWithContext
import org.jetbrains.kotlin.backend.common.extensions.IrPluginContext
import org.jetbrains.kotlin.backend.common.lower.DeclarationIrBuilder
import org.jetbrains.kotlin.backend.jvm.ir.getValueArgument
import org.jetbrains.kotlin.ir.IrStatement
import org.jetbrains.kotlin.ir.builders.*
import org.jetbrains.kotlin.ir.declarations.IrFunction
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.symbols.IrSimpleFunctionSymbol
import org.jetbrains.kotlin.ir.util.getAnnotation
import org.jetbrains.kotlin.ir.util.hasAnnotation
import org.jetbrains.kotlin.ir.util.statements
import org.jetbrains.kotlin.name.ClassId
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.name.Name

class RequiresTransformer (
    private val pluginContext: IrPluginContext,
    private val annotationClassFqName: FqName,
    private val logFunction: IrSimpleFunctionSymbol,
) : IrElementTransformerVoidWithContext() {

    val requiresAnnotation = pluginContext.referenceClass(
        ClassId(
            annotationClassFqName.parent(),
            annotationClassFqName.shortName()
        )
    )!!

    override fun visitFunctionNew(declaration: IrFunction): IrStatement {
        val body = declaration.body
        if (body != null && declaration.hasAnnotation(annotationClassFqName)) {
            val annotation = declaration.getAnnotation(annotationClassFqName)!!
            val value = annotation.getValueArgument(Name.identifier("preCond")) as IrConst<*>
            value.value.toString()
            declaration.body = irRequires(declaration, body, value)
        }
        return super.visitFunctionNew(declaration)
    }

    private fun irRequires(
        function: IrFunction,
        body: IrBody,
        preCondValue: IrConst<*>
    ): IrBlockBody {
        return DeclarationIrBuilder(pluginContext, function.symbol).irBlockBody {
            +irRequiresEnter(preCondValue)
            for (statement in body.statements) +statement
        }
    }

    private fun IrBuilderWithScope.irRequiresEnter(
        preCondVal: IrConst<*>
    ): IrCall {
        val concat = irConcat()
        concat.addArgument(irString("Wubba lubba dub dub: ${preCondVal.value}"))

        return irCall(logFunction).also { call ->
            call.putValueArgument(0, concat)
        }
//        IrIfThenElseImpl(startOffset, endOffset, ).also { irIfThenElseImpl ->
//            irIfThenElseImpl.
//        }
        TODO("Not Implemented")
    }
}
