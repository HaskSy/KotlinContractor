package org.example.contractor

import com.google.auto.service.AutoService
import org.gradle.api.Project
import org.gradle.api.provider.Provider
import org.jetbrains.kotlin.gradle.plugin.KotlinCompilation
import org.jetbrains.kotlin.gradle.plugin.KotlinCompilerPluginSupportPlugin
import org.jetbrains.kotlin.gradle.plugin.SubpluginArtifact
import org.jetbrains.kotlin.gradle.plugin.SubpluginOption

@AutoService(KotlinCompilerPluginSupportPlugin::class)
class KotlinContractorGradlePlugin : KotlinCompilerPluginSupportPlugin {
    override fun apply(target: Project) {
        target.extensions.create(
            "kotlinContractor",
            KotlinContractorGradleExtention::class.java
        )
    }

    override fun isApplicable(kotlinCompilation: KotlinCompilation<*>): Boolean = true

    override fun getCompilerPluginId(): String = BuildConfig.KOTLIN_PLUGIN_ID

    override fun getPluginArtifact(): SubpluginArtifact = SubpluginArtifact(
        groupId = BuildConfig.KOTLIN_PLUGIN_GROUP,
        artifactId = BuildConfig.KOTLIN_PLUGIN_NAME,
        version = BuildConfig.KOTLIN_PLUGIN_VERSION
    )

    override fun applyToCompilation(
        kotlinCompilation: KotlinCompilation<*>
    ): Provider<List<SubpluginOption>> {
        kotlinCompilation.dependencies {
            compileOnly("${BuildConfig.ANNOTATION_LIBRARY_GROUP}:${BuildConfig.ANNOTATION_LIBRARY_NAME}:${BuildConfig.ANNOTATION_LIBRARY_VERSION}")
        }
        val project = kotlinCompilation.target.project
        val extension = project.extensions.getByType(KotlinContractorGradleExtention::class.java)
        return project.provider {
            listOf(
                SubpluginOption(key = "enabled", value = extension.enabled.toString()),
            )
        }
    }
}
