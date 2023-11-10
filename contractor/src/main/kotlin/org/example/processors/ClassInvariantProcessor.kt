package org.example.processors

import com.google.devtools.ksp.getDeclaredFunctions
import com.google.devtools.ksp.processing.CodeGenerator
import com.google.devtools.ksp.processing.KSPLogger
import com.google.devtools.ksp.processing.Resolver
import com.google.devtools.ksp.processing.SymbolProcessor
import com.google.devtools.ksp.symbol.*
import com.google.devtools.ksp.validate
import com.squareup.kotlinpoet.*
import com.squareup.kotlinpoet.ksp.toTypeName
import com.squareup.kotlinpoet.ksp.writeTo

import org.example.annotations.ClassInvariant

class ClassInvariantProcessor(
    private val codeGenerator: CodeGenerator,
    private val logger: KSPLogger
) : SymbolProcessor {
    override fun process(resolver: Resolver): List<KSAnnotated> {
        val symbols = ClassInvariant::class.qualifiedName?.let {
            resolver.getSymbolsWithAnnotation(it)
        }
        symbols?.let { symbol ->
            symbol.filter { it is KSClassDeclaration && it.validate() }
                .forEach { it.accept(ClassInvariantVisitor(codeGenerator, logger), Unit) }
        }
        return symbols?.filter { !it.validate() }?.toList( ) ?: emptyList()
    }
}

class ClassInvariantVisitor(
    private val codeGenerator: CodeGenerator,
    private val logger: KSPLogger
) : KSVisitorVoid() {

    private val functions = mutableListOf<Func>()

    override fun visitClassDeclaration(classDeclaration: KSClassDeclaration, data: Unit) {
        classDeclaration.getDeclaredFunctions().forEach { it.accept(this, Unit) }
        val packageName = classDeclaration.packageName.asString()
        val className = "ClassInvariant$classDeclaration"
        val fileSpec = FileSpec.builder(packageName, className).apply {
            addType(
                TypeSpec.classBuilder(className)
                    .primaryConstructor(
                        FunSpec.constructorBuilder()
                            .addParameter(getConstructorParams(classDeclaration))
                            .build()
                    ).addProperty(PropertySpec
                        .builder("$classDeclaration".lowercase(), getTypeName(classDeclaration))
                        .initializer("$classDeclaration".lowercase()).build()
                    ).addSuperinterface(getTypeName(classDeclaration))
                    .addModifiers(KModifier.OPEN, KModifier.PUBLIC)
                    .addFunctions(getAllFunctions(classDeclaration)).build()
            )
        }.build()
        fileSpec.writeTo(codeGenerator, true)
    }

    override fun visitFunctionDeclaration(function: KSFunctionDeclaration, data: Unit) {
        functions.add(Func(function.toString()))
        function.returnType!!.accept(this, Unit)
    }

    override fun visitTypeReference(typeReference: KSTypeReference, data: Unit) {
        functions.firstOrNull {
            it.functionName == typeReference.parent.toString()
        }?.returnType = typeReference
    }

    private fun getAllFunctions(classDeclaration: KSClassDeclaration): Iterable<FunSpec> {
        val funSpecs = mutableListOf<FunSpec>()
        functions.forEach {
            val returnType = it.returnType!!.toTypeName()
            val paramName = classDeclaration.toString().lowercase()
            funSpecs.add(
                FunSpec.builder(it.functionName)
                    .addModifiers(KModifier.OVERRIDE)
                    .returns(returnType)
                    .addStatement("return $paramName.${it.functionName}()")
                    .build()
            )
        }
        return funSpecs
    }

    private fun getConstructorParams(classDeclaration: KSClassDeclaration): ParameterSpec {
        return ParameterSpec("$classDeclaration".lowercase(), getTypeName(classDeclaration))
    }

    private fun getTypeName(classDeclaration: KSClassDeclaration): TypeName {
        return ClassName(classDeclaration.packageName.asString(), "$classDeclaration")
    }

}

data class Func(
    val functionName: String,
    var returnType: KSTypeReference? = null
)
