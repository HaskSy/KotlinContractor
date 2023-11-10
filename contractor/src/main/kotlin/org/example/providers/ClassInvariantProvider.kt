package org.example.providers

import com.google.devtools.ksp.processing.SymbolProcessor
import com.google.devtools.ksp.processing.SymbolProcessorEnvironment
import com.google.devtools.ksp.processing.SymbolProcessorProvider
import org.example.processors.ClassInvariantProcessor

class ClassInvariantProvider : SymbolProcessorProvider {
    override fun create(environment: SymbolProcessorEnvironment): SymbolProcessor {
        return ClassInvariantProcessor(environment.codeGenerator, environment.logger)
    }
}
