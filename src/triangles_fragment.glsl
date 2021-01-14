uniform vec3 lightPos1, lightPos2,lightPos3;
uniform float specular, shininess;

in vec3 normal, halfVector1, halfVector2,halfVector3;
in vec4 diffuse, ambient, m_position;

out vec4 FragColor;

void main(){
  vec3 halfV, lightDir;
  float NdotL, NdotHV;

  // The ambient term will always be present.
  vec4 color = ambient;

  lightDir = normalize(lightPos1 - m_position.xyz);
  NdotL = dot(normal, lightDir);
  if (NdotL > 0.0) {
    color += diffuse * NdotL;
    halfV = normalize(halfVector1);
    NdotHV = abs(dot(normal, halfV));
    color += specular * pow(NdotHV, shininess);
  }
  lightDir = normalize(lightPos2 - m_position.xyz);
  NdotL = dot(normal, lightDir);
  if (NdotL > 0.0) {
    color += diffuse * NdotL;
    halfV = normalize(halfVector2);
    NdotHV = abs(dot(normal, halfV));
    color += specular * pow(NdotHV, shininess);
  }
  lightDir = normalize(lightPos3 - m_position.xyz);
  NdotL = dot(normal, lightDir);
  if (NdotL > 0.0) {
    color += diffuse * NdotL;
    halfV = normalize(halfVector3);
    NdotHV = abs(dot(normal, halfV));
    color += specular * pow(NdotHV, shininess);
  }
  FragColor = color;
}
