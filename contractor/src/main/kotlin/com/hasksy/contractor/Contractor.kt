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

        val messageList: MutableList<String> = mutableListOf("List of Contract Violations:\n")

        requiresList.forEachIndexed { index, lambda ->
            if (!lambda()) messageList.add("[Requires Error]: Pre-condition №${index+1} not satisfied")
        }

        ensuresList.forEachIndexed { index, lambda ->
            if (!ensuresCtx.lambda()) messageList.add("[Ensures Error ]: Post-condition №${index+1} not satisfied")
        }

        if (messageList.size > 1) {
            throw ContractInvalidationException(
                messageList.joinToString("\n")
            )
        }
    }
}

//class Contextualized() {
//    var savedCount = 0; var loadedCount = 0
//    var isVerifying = false
//    val stash : MutableList<Any> = mutableListOf()
//    val requiresList: MutableList<() -> Boolean> = mutableListOf()
//    val ensuresList: MutableList<EnsuresContext.() -> Boolean> = mutableListOf()
//
//    val ensuresCtx: EnsuresContext = object : EnsuresContext {
//        override fun <U : Any> old(value: U): U {
//            if (!isVerifying) {
//                stash.add(savedCount++, value)
//                return value
//            }
//            @Suppress("UNCHECKED_CAST") // should never occur
//            return stash[loadedCount++] as U
//        }
//    };
//    val ctx: ContractContext = object : ContractContext {
//        override fun requires(precondition: () -> Boolean) {
//            requiresList.add(precondition)
//            if (!precondition()) {
//                System.err.println("Precondition is not satisfied, unexpected behaviour might occur")
////                logger.warn { "Precondition is not satisfied, unexpected behaviour might occur" }
//            }
//        }
//
//        override fun ensures(postcondition: EnsuresContext.() -> Boolean) {
//            ensuresList.add(postcondition)
//            ensuresCtx.postcondition() // If there's function 'old' - calls it
//        }
//    };
//
//}
//fun contract(init: ContractContext.() -> Unit) : Contextualized? {
//    if (!KotlinContractorAssertions.ENABLED) {
//        return null
//    }
//
//    val objectCtx = Contextualized()
//    objectCtx.ctx.init();
//    return objectCtx;
//}
//
//infix fun <T> Contextualized?.execute(body: () -> T) : T {
//    if (this == null) {
//        return body();
//    }
//    try {
//        return body();
//    } finally {
//        isVerifying = true
//
//        val messageList: MutableList<String> = mutableListOf("List of Contract Violations:\n")
//
//        requiresList.forEachIndexed { index, lambda ->
//            if (!lambda()) messageList.add("[Requires Error]: Pre-condition №${index+1} not satisfied")
//        }
//
//        ensuresList.forEachIndexed { index, lambda ->
//            if (!ensuresCtx.lambda()) messageList.add("[Ensures Error ]: Post-condition №${index+1} not satisfied")
//        }
//
//        if (messageList.size > 1) {
//            throw ContractInvalidationException(
//                messageList.joinToString("\n")
//            )
//        }
//    }
//}
