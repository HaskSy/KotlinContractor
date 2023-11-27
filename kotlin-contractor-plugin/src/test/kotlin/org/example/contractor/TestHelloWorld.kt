package org.example.contractor

import com.tschuchort.compiletesting.KotlinCompilation
import com.tschuchort.compiletesting.SourceFile
import org.jetbrains.kotlin.compiler.plugin.ExperimentalCompilerApi
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class IrPluginTest {
    @OptIn(ExperimentalCompilerApi::class)
    @Test
    fun `IR plugin success`() {
        val result = compile(
            sourceFile = SourceFile.kotlin(
                "main.kt", """
fun main() { 
  println(debug())
}
fun debug() = "Hello, World!"
"""
            ),
            plugin = KotlinContractorComponentRegistrar(true)
        )
        assertEquals(KotlinCompilation.ExitCode.OK, result.exitCode)
    }
}
