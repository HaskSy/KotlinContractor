package org.example.contractor.annotations

import com.tschuchort.compiletesting.KotlinCompilation
import com.tschuchort.compiletesting.SourceFile
import org.example.contractor.KotlinContractorComponentRegistrar
import org.example.contractor.assertFunction
import org.example.contractor.invokeMain
import org.example.contractor.javaCode
import org.jetbrains.kotlin.compiler.plugin.CompilerPluginRegistrar
import org.jetbrains.kotlin.compiler.plugin.ExperimentalCompilerApi
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class TestEchoAnnotation {
    private val main = SourceFile.kotlin(
        "main.kt", """
import org.example.contractor.Echo
import org.example.contractor.Requires

fun main() {
    println(greet())
    println(greet(name = "Kotlin IR"))
    doSomething()
}

@Echo
fun greet(greeting: String = "Hello", name: String = "World"): String {
    Thread.sleep(15)
    return "${'$'}greeting, ${'$'}name!"
}

@Requires("Testing if it reads string")
@Echo
fun doSomething() {
    Thread.sleep(15)
}
"""
    )

    @OptIn(ExperimentalCompilerApi::class)
    @Test
    fun testPluginEnabled() {
        val result = compile(sourceFile = main, KotlinContractorComponentRegistrar(true))
        assertEquals(KotlinCompilation.ExitCode.OK, result.exitCode)

        val javaCode = result.javaCode("MainKt")

        assertFunction(javaCode, "public static final String greet",
            """
      public static final String greet(@NotNull final String greeting, @NotNull final String name) {
          Intrinsics.checkNotNullParameter(greeting, "greeting");
          Intrinsics.checkNotNullParameter(name, "name");
          System.out.println((Object)("⇢ greet(greeting=" + greeting + ", name=" + name + ')'));
          final TimeMark markNow = TimeSource.Monotonic.INSTANCE.markNow();
          try {
              Thread.sleep(15L);
              final String string = greeting + ", " + name + '!';
              System.out.println((Object)("⇠ greet [" + (Object)Duration.toString-impl(markNow.elapsedNow-UwyO8pc()) + "] = " + string));
              return string;
          }
          catch (final Throwable t) {
              System.out.println((Object)("⇠ greet [" + (Object)Duration.toString-impl(markNow.elapsedNow-UwyO8pc()) + "] = " + t));
              throw t;
          }
      }
      """.trimIndent())

        assertFunction(javaCode, "public static final void doSomething",
            """
      public static final void doSomething() {
          System.out.println((Object)"⇢ doSomething()");
          final TimeMark markNow = TimeSource.Monotonic.INSTANCE.markNow();
          try {
              Thread.sleep(15L);
              System.out.println((Object)("⇠ doSomething [" + (Object)Duration.toString-impl(markNow.elapsedNow-UwyO8pc()) + ']'));
          }
          catch (final Throwable t) {
              System.out.println((Object)("⇠ doSomething [" + (Object)Duration.toString-impl(markNow.elapsedNow-UwyO8pc()) + "] = " + t));
              throw t;
          }
      }
      """.trimIndent())

        val out = invokeMain(result, "MainKt").trim().split("""\r?\n+""".toRegex())
        val iter = out.iterator()
        assert(out.size == 8)
        assert(iter.next() == "⇢ greet(greeting=Hello, name=World)")
        assert(iter.next() matches "⇠ greet \\[\\d+(\\.\\d+)?ms] = Hello, World!".toRegex())
        assert(iter.next() == "Hello, World!")
        assert(iter.next() == "⇢ greet(greeting=Hello, name=Kotlin IR)")
        assert(iter.next() matches "⇠ greet \\[\\d+(\\.\\d+)?ms] = Hello, Kotlin IR!".toRegex())
        assert(iter.next() == "Hello, Kotlin IR!")
        assert(iter.next() == "preCond: Testing if it reads string")
        assert(iter.next() == "⇢ doSomething()")
        assert(iter.next() matches "⇠ doSomething \\[\\d+(\\.\\d+)?ms]".toRegex())
        assert(!iter.hasNext())
    }

    @OptIn(ExperimentalCompilerApi::class)
    @Test
    fun testPluginDisabled() {
        val result = compile(sourceFile = main, plugin = KotlinContractorComponentRegistrar(false))
        assertEquals(KotlinCompilation.ExitCode.OK, result.exitCode)

        val javaCode = result.javaCode("MainKt")

        assertFunction(javaCode, "public static final String greet",
            """
      public static final String greet(@NotNull final String greeting, @NotNull final String name) {
          Intrinsics.checkNotNullParameter(greeting, "greeting");
          Intrinsics.checkNotNullParameter(name, "name");
          Thread.sleep(15L);
          return greeting + ", " + name + '!';
      }
      """.trimIndent())

        assertFunction(javaCode, "public static final void doSomething",
            """
      public static final void doSomething() {
          Thread.sleep(15L);
      }
      """.trimIndent())

        val out = invokeMain(result, "MainKt").trim().split("""\r?\n+""".toRegex())
        val iter = out.iterator()
        assert(out.size == 2)
        assert(iter.next() == "Hello, World!")
        assert(iter.next() == "Hello, Kotlin IR!")
        assert(!iter.hasNext())
    }}

@OptIn(ExperimentalCompilerApi::class)
fun compile(
    sourceFiles: List<SourceFile>,
    plugin: CompilerPluginRegistrar = KotlinContractorComponentRegistrar(),
): KotlinCompilation.Result {
    return KotlinCompilation().apply {
        sources = sourceFiles
        compilerPluginRegistrars = listOf(plugin)
        useIR = true
        inheritClassPath = true
    }.compile()
}

@OptIn(ExperimentalCompilerApi::class)
fun compile(
    sourceFile: SourceFile,
    plugin: CompilerPluginRegistrar = KotlinContractorComponentRegistrar(),
): KotlinCompilation.Result {
    return compile(listOf(sourceFile), plugin)
}
