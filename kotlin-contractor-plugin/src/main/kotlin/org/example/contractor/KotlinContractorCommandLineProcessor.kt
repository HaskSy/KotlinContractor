package org.example.contractor

import com.google.auto.service.AutoService
import org.jetbrains.kotlin.compiler.plugin.AbstractCliOption
import org.jetbrains.kotlin.compiler.plugin.CliOption
import org.jetbrains.kotlin.compiler.plugin.CommandLineProcessor
import org.jetbrains.kotlin.compiler.plugin.ExperimentalCompilerApi
import org.jetbrains.kotlin.config.CompilerConfiguration
import org.jetbrains.kotlin.config.CompilerConfigurationKey

@OptIn(ExperimentalCompilerApi::class)
@AutoService(CommandLineProcessor::class)
class KotlinContractorCommandLineProcessor : CommandLineProcessor {

    companion object {
        private const val OPTION_ENABLED = "enabled"
        val KEY_ENABLED = CompilerConfigurationKey<Boolean>(OPTION_ENABLED)
    }

    override val pluginId: String = BuildConfig.KOTLIN_PLUGIN_ID
    override val pluginOptions: Collection<AbstractCliOption> = listOf(
        CliOption(
            optionName = OPTION_ENABLED,
            valueDescription = "<true|false>",
            description = "whether plugin is enabled",
            required = false,
            allowMultipleOccurrences = false
        )
    )

    override fun processOption(
        option: AbstractCliOption,
        value: String,
        configuration: CompilerConfiguration
    ) = when (option.optionName) {
        OPTION_ENABLED -> configuration.put(KEY_ENABLED, value.toBoolean())
        else -> error("Unexpected config option ${option.optionName}")
    }
}
