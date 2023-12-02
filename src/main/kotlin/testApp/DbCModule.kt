package testApp

import kotlin.reflect.KProperty1
import kotlin.reflect.full.memberProperties
import kotlin.reflect.jvm.isAccessible

fun <T> dbc(block: ContractContext.() -> T) {
    var isVerifying: Boolean
    lateinit var ctx: ContractContext
    lateinit var requiresLambda: () -> Boolean
    lateinit var ensuresLambda: () -> Boolean

    try {
        isVerifying = false
        ctx = object : ContractContext {
            private val oldValues = mutableMapOf<String, Any?>()

            override fun requires(precondition: () -> Boolean) {
                requiresLambda = precondition
                if (!precondition()) throw IllegalArgumentException("Precondition not satisfied")
            }

            override fun ensures(postcondition: () -> Boolean) {
                postcondition()
                ensuresLambda = postcondition
            }

            override fun <V> old(obj: Any, name: String): V {
                if (!isVerifying) {
                    storeOldValue<V>(obj, name)
                }
                return oldValues[name] as? V
                    ?: throw IllegalArgumentException("No old value stored for $name or type mismatch")
            }

            override fun <V> storeOldValue(obj: Any, name: String) {
                val property = obj::class.memberProperties.first { it.name == name } as KProperty1<Any, *>
                property.isAccessible = true
                oldValues[name] = property.get(obj) as V
            }
        }
        ctx.block()

    } finally {
        isVerifying = true
        if (!requiresLambda()) throw IllegalArgumentException("Precondition not satisfied")
        if (!ensuresLambda()) throw IllegalArgumentException("Postcondition not satisfied")
    }
}

interface ContractContext {
    fun requires(precondition: () -> Boolean)
    fun ensures(postcondition: () -> Boolean)

    fun <V> old(obj: Any, name: String): V

    fun <V> storeOldValue(obj: Any, name: String)
}
