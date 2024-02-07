package com.hasksy.contractor

import kotlin.reflect.KMutableProperty1
import kotlin.reflect.KProperty1
import kotlin.reflect.jvm.isAccessible

object KotlinContractorAssertions {
    val ENABLED = System.getProperty("contractorEnabled", "false").toBoolean();
}

@DslMarker
@Target(AnnotationTarget.CLASS, AnnotationTarget.TYPE)
annotation class DbCMarker

class RequiresContractException(message: String) : RuntimeException(message);
class EnsuresContractException(message: String) : RuntimeException(message);

fun <T> dbc(thisRef: Any, block: ContractContext.() -> T): T {
    var isVerifying = false;
    val requiresList: MutableList<() -> Boolean> by lazy { mutableListOf() };
    val ensuresList: MutableList<() -> Boolean> by lazy { mutableListOf() };

    val ctx = object : ContractContext {
        private val oldValues = mutableMapOf<String, Any?>()
        override fun requires(precondition: () -> Boolean) {
            if (!KotlinContractorAssertions.ENABLED) {
                return
            }
            requiresList.add(precondition)
            if (!precondition()) {
                System.err.println("Precondition is not satisfied, unexpected behaviour might occur")
            }
        }

        override fun ensures(postcondition: () -> Boolean) {
            if (!KotlinContractorAssertions.ENABLED) {
                return
            }
            ensuresList.add(postcondition)
            postcondition() // If there's function 'old' - calls it
        }

        override fun <T> old(property: KMutableProperty1<out Any, T>): T {
            if (!isVerifying) {
                val casted = property as KProperty1<Any, T>
                storeOldValue(thisRef, casted)
            }
            return oldValues[property.name] as? T
                ?: throw IllegalArgumentException("No old value stored for ${property.name} or type mismatch")
        }

        private fun <T> storeOldValue(receiver: Any, property: KProperty1<Any, T>) {
            val oldAccessibility = property.isAccessible
            property.isAccessible = true
            oldValues[property.name] = property.get(receiver)
            property.isAccessible = oldAccessibility
        }
    }

    try {
        isVerifying = false
        return ctx.block()
    } finally {
        if (KotlinContractorAssertions.ENABLED) {
            isVerifying = true

            for (requiresLambda in requiresList) {
                if (!requiresLambda()) throw RequiresContractException("Precondition not satisfied")
            }

            for (ensuresLambda in ensuresList) {
                if (!ensuresLambda()) throw EnsuresContractException("Postcondition not satisfied")
            }
        }
    }
}

interface ContractContext {
    fun requires(precondition: () -> Boolean)
    fun ensures(postcondition: () -> Boolean)
    fun <T> old(property: KMutableProperty1<out Any, T>): T
}
