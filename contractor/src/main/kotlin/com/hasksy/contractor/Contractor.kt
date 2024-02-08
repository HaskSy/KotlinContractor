package com.hasksy.contractor

object KotlinContractorAssertions {
    val ENABLED = System.getProperty("contractorEnabled", "false").toBoolean();
}

class RequiresContractException(message: String) : RuntimeException(message);
class EnsuresContractException(message: String) : RuntimeException(message);

interface ContractContext {
    fun requires(precondition: () -> Boolean)
    fun ensures(postcondition: EnsuresContext.() -> Boolean)
}

interface EnsuresContext {
    fun <U : Any> old(value: U): U
}

val DUMMY_OBJECT = object : ContractContext {
    override fun requires(precondition: () -> Boolean) {}
    override fun ensures(postcondition: EnsuresContext.() -> Boolean) {}
}

fun <T> dbc(block: ContractContext.() -> T): T {
    if (!KotlinContractorAssertions.ENABLED) {
        return DUMMY_OBJECT.block();
    }

    var savedCount = 0; var loadedCount = 0;
    var isVerifying = false;
    val stash : MutableList<Any> = mutableListOf()
    val requiresList: MutableList<() -> Boolean> = mutableListOf();
    val ensuresList: MutableList<EnsuresContext.() -> Boolean> = mutableListOf();

    val ensuresCtx = object : EnsuresContext {
        override fun <U : Any> old(value: U): U {
            if (!isVerifying) {
                stash.add(savedCount++, value);
                return value;
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

        for (requiresLambda in requiresList) {
            if (!requiresLambda()) throw RequiresContractException("Precondition not satisfied")
        }

        for (ensuresLambda in ensuresList) {
            if (!ensuresCtx.ensuresLambda()) throw EnsuresContractException("Postcondition not satisfied")
        }
    }
}


fun check() = dbc {
    var test = 100
    requires { test < 300}
    ensures { old(test) + 100 == test}
    test += 100
    println(test)
}

fun main() {
    check()
}
