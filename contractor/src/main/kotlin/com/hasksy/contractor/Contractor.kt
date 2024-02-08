package com.hasksy.contractor

import io.github.oshai.kotlinlogging.KotlinLogging

private object KotlinContractorAssertions {
    val ENABLED = System.getProperty("contractorEnabled", "false").toBoolean();
}

private val logger = KotlinLogging.logger {}

class ContractInvalidationException(message: String) : RuntimeException(message);

interface ContractContext {
    fun requires(precondition: () -> Boolean)
    fun ensures(postcondition: EnsuresContext.() -> Boolean)
}

interface EnsuresContext {
    fun <U : Any> old(value: U): U
}

private val DUMMY_OBJECT = object : ContractContext {
    override fun requires(precondition: () -> Boolean) {}
    override fun ensures(postcondition: EnsuresContext.() -> Boolean) {}
}

fun <T> dbc(block: ContractContext.() -> T): T {
    if (!KotlinContractorAssertions.ENABLED) {
        return DUMMY_OBJECT.block()
    }

    var savedCount = 0; var loadedCount = 0
    var isVerifying = false
    val stash : MutableList<Any> = mutableListOf()
    val requiresList: MutableList<() -> Boolean> = mutableListOf()
    val ensuresList: MutableList<EnsuresContext.() -> Boolean> = mutableListOf()

    val ensuresCtx = object : EnsuresContext {
        override fun <U : Any> old(value: U): U {
            if (!isVerifying) {
                stash.add(savedCount++, value)
                return value
            }
            @Suppress("UNCHECKED_CAST") // should never occur
            return stash[loadedCount++] as U
        }
    }

    val ctx = object : ContractContext {
        override fun requires(precondition: () -> Boolean) {
            requiresList.add(precondition)
            if (!precondition()) {
                System.err.println("Precondition is not satisfied, unexpected behaviour might occur")
//                logger.warn { "Precondition is not satisfied, unexpected behaviour might occur" }
            }
        }

        override fun ensures(postcondition: EnsuresContext.() -> Boolean) {
            ensuresList.add(postcondition)
            ensuresCtx.postcondition() // If there's function 'old' - calls it
        }
    }

    try {
        isVerifying = false
        return ctx.block();
    } finally {
        isVerifying = true

        val messageList: MutableList<String> = mutableListOf()

        requiresList.forEachIndexed { index, lambda ->
            if (!lambda()) messageList.add("[Requires Error]: Pre-condition №${index+1} not satisfied")
        }

        ensuresList.forEachIndexed { index, lambda ->
            if (!ensuresCtx.lambda()) messageList.add("[Ensures Error ]: Post-condition №${index+1} not satisfied")
        }

        if (messageList.size > 0) {
            throw ContractInvalidationException(
                "List of Contract Violations:\n" + messageList.joinToString("\n")
            )
        }
    }
}
