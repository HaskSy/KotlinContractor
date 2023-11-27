package org.example.contractor

import com.google.auto.service.AutoService
import org.jetbrains.kotlin.backend.common.extensions.IrGenerationExtension
import org.jetbrains.kotlin.compiler.plugin.CompilerPluginRegistrar
import org.jetbrains.kotlin.compiler.plugin.ExperimentalCompilerApi
import org.jetbrains.kotlin.config.CompilerConfiguration


@OptIn(ExperimentalCompilerApi::class)
@AutoService(CompilerPluginRegistrar::class)
class KotlinContractorComponentRegistrar(
    private val defaultEnabled: Boolean,
) : CompilerPluginRegistrar() {
    override val supportsK2: Boolean = true

    @Suppress("unused")
    constructor() : this(
        defaultEnabled = true,
    )

    override fun ExtensionStorage.registerExtensions(configuration: CompilerConfiguration) {
        val enabled = configuration.get(KotlinContractorCommandLineProcessor.KEY_ENABLED, defaultEnabled)
        if (enabled) {
            IrGenerationExtension.registerExtension(KotlinContractorIrGenerationExtention())
        }
    }
}
